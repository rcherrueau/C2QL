module Pi

import Utils
import C2QL
import Privy

import Effects
import Effect.State
import Effect.StdIO

import Debug.Trace

%default total


-- Pi Term

||| Translation of query.Pred
data QPred = AND QPred QPred
           | OR QPred QPred
           | Like Attribute String
           | NextWeek Attribute
           | Equal Attribute String

||| Translation of query.Pred
data Q = Rel String
       | Project Schema Q
       | Product Q Q
       | NJoin Q Q
       | Count Schema Q
       | Select QPred  Q
       | Decrypt Attribute CryptTy Q
       | Defrag Q Q

||| Name and Relation into the piterm
data L = MkN String | MkR String Schema

||| piterm for C2QL
data Pi = Rcv L (List L) Pi
        | Send L (List L) Pi
        | Par Pi Pi
        | NewN L Pi
        | Rep Pi
        | Guard L L Pi
        | NewR L Pi
        | Let L Q Pi
        | End


-- Show instances

Show QPred where
  show (AND x y)    = show x ++ " && " ++ show y
  show (OR x y)     = show x ++ " || " ++ show y
  show (Like x y)   = show@{attr} x ++ " like " ++ y
  show (NextWeek x) = show@{attr} x ++ " >= 8 days"
  show (Equal x y)  = show@{attr} x ++ " == " ++ y

Show Q where
  show (Rel x)         = x
  show (Project x y)   = "π " ++ show@{sch} x ++ " " ++ show y
  show (Product x y)   = show x ++ " * " ++ show y
  show (NJoin x y)     = show x ++ " |><| " ++ show y
  show (Count x y)     = "count " ++ show@{sch} x ++ " " ++ show y
  show (Select x y)    = "σ (" ++ show x ++ ") " ++ show y
  show (Decrypt y _ w) = "decrypt " ++ show@{attr} y ++ " " ++ show w
  show (Defrag x y)    = "defrag " ++ show x ++ " " ++ show y

Show L where
  show (MkN x)   = x
  show (MkR x y) = x ++ ":" ++ show@{sch} y

[ls] Show (List L) where
  show = concat . intersperse ", " . map show

Show Pi where
  show (Rcv x xs y)  = show x ++ "(" ++ (show@{ls} xs) ++ ")." ++ show y
  show (Send x xs y) = show x ++ "<" ++ show@{ls} xs ++ ">." ++ show y
  show (Par x y)     = "(" ++ show x ++ ")|" ++ show y
  show (NewN x y)    = "(ν"++ show x ++")" ++ show y
  show (Rep x)       = "!" ++ show x
  show (Guard x y z) = "["++ show x ++ "=" ++ show y ++"]" ++ show z
  show (NewR x y)    = "(ρ"++ show x ++")" ++ show y
  show (Let x y z)   = "let " ++ show x ++
                       " = ("  ++ show y ++ ") in " ++ show z
  show End           = "0"


-- Utils

mkNewNApp : (a : Maybe Pi) -> (k : Pi) -> Pi
mkNewNApp Nothing  k = k
mkNewNApp (Just _) k = (NewN (MkN "app") k)

mkNewNFrags : (f : List Pi) -> (k : Pi) -> Pi
mkNewNFrags [] k = (NewN (MkN "db") k)
mkNewNFrags fs k = snd $
  foldr (\_,(n,k) => (S n, NewN (MkN ("frag_" ++ show n)) k)) (Nat.Z,k) fs

||| Puts many Pi term in parallel with Pi.Par.
|||
||| The last of the list is put in parallel with `k`.
parStar : List Pi -> (k : Pi) -> Pi
parStar = flip $ foldr Par


-- Translation C2QL → Pi
toQPred : C2QLPred -> QPred
toQPred (AND x y)    = AND (toQPred x) (toQPred y)
toQPred (OR x y)     = OR (toQPred x) (toQPred y)
toQPred (Like a pat) = Like a pat
toQPred (NextWeek a) = NextWeek a
toQPred (Equal a v)  = Equal a (show v)

-- Translation with a parallel strategy.
namespace parallel
  ||| Translates a C2QL terms into a Pi term with a parallele
  ||| strategy.
  |||
  ||| @ h Name of the request.
  ||| @ q C2QL term to translate.
  toPi : (h : String) -> (q : C2QL) -> Pi
  toPi h q = let maybeApp  = map Rep (toApp h q)
                 frags     = map Rep (toFrag h q)
                 client    = toClient h (length frags) q
             in (mkNewNApp maybeApp
                (mkNewNFrags frags
                (NewN (MkN "client")
                  (Par (fromMaybe End maybeApp)
                       (parStar frags client))))) where

    ||| Makes the application Pi term of the C2QL term.
    |||
    ||| App acts as a proxy between the database and the client.
    toApp : (h : String) -> C2QL -> Maybe Pi
    toApp h q = let pi = runPure (toApp' q)
                in pure $
                Rcv (MkN "app") [MkN "url"] (
                  Guard (MkN "url") (MkN h) !pi) where
      toApp' : C2QL -> UID (Maybe Pi)
      toApp' (Project _ q)       = toApp' q
      toApp' (Product q1 q2)     = toApp' q1 <|> toApp' q2
      toApp' (NJoin q1 q2)       = toApp' q1 <|> toApp' q2
      toApp' (Count _ q)         = toApp' q
      toApp' (Select _ q)        = toApp' q
      toApp' (Crypt _ _ q)       = toApp' q
      toApp' (Decrypt a c q)     = do
        maybeDefrag <- toApp' q
        pure (maybeDefrag
              <|> Just (Send (MkN "db") [MkN "url", MkN "client"] End))
      toApp' (Frag _ q)          = toApp' q
      toApp' (Defrag (ql, Defrag x y) _) = do
        let qr = Defrag x y
        idl  <- mkSym "frag_"
        qrPi <- assert_total $ toApp' qr
        pure $ do
          qrPi' <- qrPi
          pure (Par (Send (MkN "fragi") [MkN "url", MkN "client"] End) qrPi')
      toApp' (Defrag (ql, qr) _) = do
        idl <- mkSym "frag_"
        idr <- mkSym "frag_"
        pure $
          Just (Par (Send (MkN idl) [MkN "url", MkN "client"] End)
                    (Send (MkN idr) [MkN "url", MkN "client"] End))
      toApp' (Rel _)             = pure Nothing
      toApp' (Hole_ _)           = pure Nothing

    ||| Makes the client Pi term of the C2QL term.
    toClient : (h : String) -> (nbFrag : Nat) -> C2QL -> Pi
    toClient h nbFrag q =
      let kpi = runPureInit ['At := Bot, 'UIDVar := Z, 'Ctx := []]
                            (toClient' q)
      in kpi End where
      toClient' : C2QL -> { [
                     'At     ::: STATE Place,
                     'UIDVar ::: STATE Nat,
                     'Ctx    ::: STATE (List String) ] } Eff (Pi -> Pi)
      toClient' (Select p q)        = do
        kpi <- toClient' q
        if List.elem !('At :- get) [Client, Bot]
        then (do
          rel <- Rel <$> 'Ctx :- pop
          id  <- 'UIDVar :- mkSym "r_"
          'Ctx :- push id
          -- XXX Report bug: (.) produces segfault
          -- pure $ Let (MkN id) (Select (toQPred p) rel) . kpi)
          pure $ \pi => kpi $ Let (MkN id) (Select (toQPred p) rel) pi)
        else pure kpi
      toClient' (Project δ q)       = do
        kpi <- toClient' q
        if List.elem !('At :- get) [Client, Bot]
        then (do
          rel <- Rel <$> 'Ctx :- pop
          id  <- 'UIDVar :- mkSym "r_"
          'Ctx :- push id
          pure $ \pi => kpi $ Let (MkN id) (Project δ rel) pi)
        else pure kpi
      toClient' (Count δ q)         = do
        kpi <- toClient' q
        if List.elem !('At :- get) [Client, Bot]
        then (do
          rel <- Rel <$> 'Ctx :- pop
          id  <- 'UIDVar :- mkSym "r_"
          'Ctx :- push id
          pure $ \pi => kpi $ Let (MkN id) (Count δ rel) pi)
        else pure kpi
      toClient' (Rel δ)             = do
        if !('At :- get) == Bot
        then (do
          id  <- 'UIDVar :- mkSym "r_"
          'Ctx :- push id
          pure $ \pi => NewR (MkR id δ) pi)
        else pure id
      -- C2QL destructor
      toClient' (Decrypt a c q)     = do
        kpi <- toClient' q
        if List.elem !('At :- get) [Client, Bot]
        then (do
          rel <- Rel <$> 'Ctx :- pop
          id  <- 'UIDVar :- mkSym "r_"
          'Ctx :- push id
          pure $ \pi => kpi $ Let (MkN id) (Decrypt a c rel) pi)
        else (do
          idRcv  <- 'UIDVar :- mkSym "r_"
          idLet  <- 'UIDVar :- mkSym "r_"
          'Ctx :- push idLet
          'At  :- put Client
          pure $ \pi => kpi $
            Send (MkN "app") [MkN h] (
              Rcv (MkN "client") [MkN idRcv] (
                Let (MkN idLet) (Decrypt a c (Rel idRcv)) pi)))
      toClient' (Defrag _ q) = (do
        kpi <- toClient' q
        let sendAppPi = \pi => kpi (Send  (MkN "app") [MkN h] pi)
        -- Construct all the receive continuation
        rcvPis <- sequence $ List.replicate nbFrag (do
          idRcv <- 'UIDVar :- mkSym "r_"
          'Ctx :- push idRcv
          pure $ \pi => Rcv (MkN "client") [MkN idRcv] pi)
        -- Then makes all relation Q term using the context
        rels <- sequence $ List.replicate nbFrag (Rel <$> 'Ctx :- pop)
        -- And construct the Defrag pi term from these rels
        idLet  <- 'UIDVar :- mkSym "r_"
        let defLet = \pi => Let (MkN idLet)
                                (foldr Defrag (last rels) (init rels)) pi
        'Ctx :- push idLet
        'At  :- put Client
        -- Chain all receives together and finish with the let.
        let rcvPi = foldr (\pik,r => \pi => pik $ r pi) defLet rcvPis
        -- Finally, add the sendApp term and construct the final term.
        pure (\pi => kpi $ Send (MkN "app") [MkN h] $ rcvPi pi)) where
          init : List a -> List a
          init []        = []
          init [x]       = []
          init (x :: xs) = x :: (init xs)

          last : List Q -> Q
          last []        = Rel "error"
          last [x]       = x
          last (x :: xs) = last xs
      -- C2QL spec
      toClient' (Frag δ q)          = do
        toClient' q
        'At :- put (Frag Z)
        pure id
      toClient' (Crypt a c q)       = do
        toClient' q
        'At :- put (Frag Z)
        pure id
      toClient' _                   = pure id
      -- No implemented: sorry bro!
      -- toClient' (Product q1 q2)     pi = ?todo_product
      -- toClient' (NJoin q1 q2)       pi = ?todo_njoins

    ||| Makes the database Pi term of the C2QL term.
    toFrag : (h : String) -> C2QL -> List Pi
    toFrag h q = ?mlkj {- runPure  (toFrag' q) -} where
      toFrag' : C2QL -> (fId : Fin n) -> UID (Vect n (Pi -> Pi))
      toFrag' (Project x y)   fId =
      toFrag' (Product x y)   fId = ?to_rhs_2
      toFrag' (NJoin x y)     fId = ?to_rhs_3
      toFrag' (Count x y)     fId = ?to_rhs_4
      toFrag' (Select x y)    fId = ?to_rhs_5
      toFrag' (Crypt x y z)   fId = ?to_rhs_6
      toFrag' (Decrypt x y z) fId = ?to_rhs_7
      toFrag' (Frag x y)      fId = ?to_rhs_8
      toFrag' (Defrag x y)    fId = ?to_rhs_9
      toFrag' (Rel x)         fId = ?to_rhs_10
      toFrag' (Hole_ k)       fId = ?to_rhs_11

-- namespace sequential
--   toApp : (h : String) -> C2QL -> Pi

-- agendaPi : Pi
-- agendaPi =
--   Rcv (MkN "app") [MkN "url"] (
--   Guard (MkN "url") (MkN "adresse") (
--   Par (Send (MkN "fragg") [MkN "url", MkN "client"] End)
--       (Send (MkN "fragd") [MkN "url", MkN "client"] End)))

-- fraggPi : Pi
-- fraggPi =
--   NewR (MkR "rdvg" [D,Id]) (
--   Rcv (MkN "fragg") [MkN "url", MkN "k"] (
--   Guard (MkN "url") (MkN "adresse") (
--   Let (MkN "s") (Project [Id] (Rel "rdvg")) (
--   Send (MkN "k") [MkN "s"] End))))

-- fragdPi : Pi
-- fragdPi =
--   NewR (MkR "rdvd" [N_AES,A,Id]) (
--   Rcv (MkN "fragd") [MkN "url", MkN "k"] (
--   Guard (MkN "url") (MkN "adresse") (
--   Let (MkN "s") (Project [N_AES,A,Id] (Rel "rdvg")) (
--   Send (MkN "k") [MkN "s"] End))))

-- alicePi : Pi
-- alicePi =
--   Send (MkN "app") [MkN "adresse"] (
--   Rcv (MkN "client") [MkN "r1"] (
--   Rcv (MkN "client") [MkN "r2"] (
--   Let (MkN "s") (Defrag (Rel "r1") (Rel "r2")) (
--   Let (MkN "t") (Decrypt N_AES AES (Rel "s")) (
--   Let (MkN "u") (Select (Like N "C*") (Rel "t")) End)))))

-- adressePi : Pi
-- adressePi =
--   (NewN (MkN "app") (NewN (MkN "fragg")
--   (NewN (MkN "fragd") (NewN (MkN "client")
--     (Par (Rep agendaPi)
--     (Par (Rep fraggPi)
--     (Par (Rep fragdPi) (Rep alicePi))))))))


qaddrAgendaPi : Pi
qaddrAgendaPi = parallel.toPi "adresse" qaddrC2QL'

main : IO ()
main = do -- printLn adressePi
          putStrLn "-------------- [Agenda]"
          printLn qaddrC2QL'
          printLn qaddrAgendaPi
          putStrLn "-------------- [Tests]"
          let q1 = runPure (toC2QL qaddr)
          printLn q1
          printLn (parallel.toPi "test" q1)


-- Local Variables:
-- eval: (setq idris-interpreter-path (expand-file-name "./linkIdris11"))
-- idris-load-packages: ("effects")
-- End:
