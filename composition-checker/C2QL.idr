module C2QL

import Privy
import Utils

import Debug.Trace
%default total
%access export


-- C2QL Term

public export
data C2QLPred : Type where
  AND      : C2QLPred -> C2QLPred -> C2QLPred
  OR       : C2QLPred -> C2QLPred -> C2QLPred
  Like     : Attribute -> String -> C2QLPred
  NextWeek : Attribute -> C2QLPred
  Equal    : (a : Attribute) -> (v : interpTy (snd a)) ->
             Eq (interpTy (snd a)) => Show (interpTy (snd a)) => C2QLPred

public export
data C2QL : Type where
  Project : Schema -> C2QL -> C2QL
  Product : C2QL -> C2QL -> C2QL
  NJoin   : C2QL -> C2QL -> C2QL
  Count   : Schema -> C2QL -> C2QL
  Select  : C2QLPred -> C2QL -> C2QL
  -- C2QL specific
  Crypt   : Attribute -> CryptTy -> C2QL -> C2QL
  Decrypt : Attribute -> CryptTy -> C2QL -> C2QL
  Frag    : Schema -> C2QL -> C2QL
  Defrag  : (C2QL, C2QL) -> C2QL -> C2QL
  Rel     : Schema -> C2QL
  Hole_   : Nat -> C2QL


-- Implementations for C2QL

Show C2QLPred where
  show (AND x y)    = show x ++ " && " ++ show y
  show (OR x y)     = show x ++ " || " ++ show y
  show (Like x y)   = show@{attr} x ++ " like " ++ y
  show (NextWeek x) = show@{attr} x ++ " >= 8 days"
  show (Equal x y)  = show@{attr} x ++ " == " ++ show y

Show C2QL where
  show x = showQ x where

    showK : C2QL -> String
    showK (Rel δ) = "  R" ++ show@{sch} δ
    showK q       = " ∘ " ++ show q

    showQ : C2QL -> String
    showQ (Project δ q)       = "π " ++ show@{sch} δ ++ showK q
    showQ (Product q1 q2)     = "(" ++ showQ q1 ++ " ⨯ " ++ showQ q2 ++ ")"
    showQ (NJoin q1 q2)       = "(" ++ showQ q1 ++ " ⨝ " ++ showQ q2 ++ ")"
    showQ (Count δ q)         = "count " ++ show@{sch} δ ++ showK q
    showQ (Select p q)        = "σ (" ++ show p ++ ")" ++ showK q
    showQ (Crypt a c q)       =
      "crypt " ++ show@{attr} a ++ " " ++ show c ++ showK q
    showQ (Decrypt a c q)     =
      "decrypt " ++ show@{attr} a ++ " " ++ show c ++ showK q
    showQ (Frag δ q)          = "frag " ++ show@{sch} δ ++ showK q
    showQ (Defrag (ql, qr) q) =
      let qlShow = assert_total $ show ql
          qrShow = assert_total $ show qr
      in "defrag (" ++ qlShow ++ ", " ++ qrShow ++ ")" ++ showK q
    showQ (Rel δ)             = "R" ++ show@{sch} δ
    showQ (Hole_ x)           = "id_" ++ show x

Eq C2QLPred where
    (AND x z)     == (AND y w)     = x == y && z  == w
    (OR x z)      == (OR y w)      = x == y && z  == w
    (Like x z)    == (Like y w)    = x == y && z  == w
    (NextWeek x)  == (NextWeek y)  = x == y
    (Equal a v)   == (Equal x y)   = a == x &&
                                     -- if a == x, then Ty of a == Ty
                                     -- of x, so interTy of Ty of a ==
                                     -- interpTy of Ty of x. TODO: Go
                                     -- with a `DecEq` rather than
                                     -- `believe_me`
                                     v == (believe_me (interpTy (snd a)) y)
    _             == _             = False

Eq C2QL where
    (Project x z)    == (Project y w)    = x == y && z == w
    (Product x z)    == (Product y w)    = x == y && z == w
    (NJoin x z)      == (NJoin y w)      = x == y && z == w
    (Count x z)      == (Count y w)      = x == y && z == w
    (Select x z)     == (Select y w)     = z == w && x == y
    (Crypt x z w)    == (Crypt y s t)    = x == y && z == s && w == t
    (Decrypt x z w)  == (Decrypt y s t)  = x == y && z == s && w == t
    (Frag x z)       == (Frag y w)       = x == y && z == w
    (Defrag x z)     == (Defrag y w)     = assert_total (x == y) && z == w
    (Rel x)          == (Rel y)          = x == y
    (Hole_ k)        == (Hole_ j)        = k == j
    _                == _                = False


-- Utils

||| Fills the term `t` with the term `f` at the hole `h`.
c2qlFillHole : (t : C2QL) -> (h : C2QL) -> (f : C2QL) -> C2QL
c2qlFillHole (Project x t) h f       = Project x (c2qlFillHole t h f)
c2qlFillHole (Product x t) h f       = Product x (c2qlFillHole t h f)
c2qlFillHole (NJoin t1 t2) h f       =
  let t1' = c2qlFillHole t1 h f
      t2' = c2qlFillHole t2 h f
  in NJoin t1' t2'
c2qlFillHole (Count x t) h f         = Count x (c2qlFillHole t h f)
c2qlFillHole (Select x t) h f        = Select x (c2qlFillHole t h f)
c2qlFillHole (Crypt x y t) h f       = Crypt x y (c2qlFillHole t h f)
c2qlFillHole (Decrypt x y t) h f     = Decrypt x y (c2qlFillHole t h f)
c2qlFillHole (Frag x t) h f          = Frag x (c2qlFillHole t h f)
c2qlFillHole (Defrag (t1,t2) t3) h f =
  let t1' = assert_total $ c2qlFillHole t1 h f
      t2' = assert_total $ c2qlFillHole t2 h f
      t3' = c2qlFillHole t3 h f
  in Defrag (t1', t2') t3
c2qlFillHole (Hole_ x) h f with (h == Hole_ x)
  c2qlFillHole (Hole_ x) h f | False = Hole_ x
  c2qlFillHole (Hole_ x) h f | True  = f
c2qlFillHole t h f                   = t


-- Translation Privy → C2QL

using (Δ : Schema, Δ' : Schema, δ : Schema, δ' : Schema,
 Δs : Vect n Schema,
 env : Env n , env' : Env m , env'' : Env k) {

||| Translates a Privy term into a C2QL term.
|||
||| The translation is partial since a Privy term is more powerful
||| than a C2QL one. Rules to follow to ensure that the transformation
||| goes well is:
||| - Do only one query per fragment and per term.
||| - Use a variable only once (similar to a linear type system).
toC2QL : Privy env env' Δ -> UID C2QL
toC2QL p {env} {env'} = (do
   init <- envToC2QL env
   incrAfter fragSize -- Firsts ids of UID are reserved for
                      -- fragments. The rest is for variables.
   privyToC2QL p init) where


  ||| Returns the number of fragments in the Privy term
  fragSize : Nat
  fragSize = length env'

  ||| Translates an environment into a C2QL term.
  |||
  ||| Generates the intial structure for the C2QL term. There is two
  ||| cases:
  ||| - It starts from an unfragmented environment, then the most
  |||   right term is the relation with schema δ.
  ||| - It starts from a fragmented environment, then the most right
  |||   term is the combination of defrag/frag over the relation. The
  |||   relation is the concatenation of all attributes in all
  |||   fragmentes.
  ||| This also introduce crypt term if the environment includes
  ||| encrypted attributes.
  -- TODO: Manage the case for encryption
  envToC2QL : Env n -> UID C2QL
  envToC2QL [δ] = pure $ Rel δ
  envToC2QL δs@(_ :: _ :: _)  = let rel = Rel [δ | δ <- concat δs, δ /= Id]
                                in envToC2QL' δs rel where
    envToC2QL' : Env (S n) -> C2QL -> UID C2QL
    envToC2QL' [δ, δ']               c = do
      id <- freshId
      pure $ Defrag (Hole_ id, Hole_ (S id)) $ c
    envToC2QL' δs@(w :: x :: y :: z) c = do
      id <- freshId
      let env = tail δs
      let c'  = Hole_ (id + fragSize)
      rec <- envToC2QL' env c'
      pure $ Defrag (Hole_ id, rec) c

  ||| Returns True if the current C2QL term contains, at least, one
  ||| Defrag.
  hasDefrag : C2QL -> Bool
  hasDefrag (Project x y)   = hasDefrag y
  hasDefrag (Product x y)   = hasDefrag x || hasDefrag y
  hasDefrag (NJoin x y)     = hasDefrag x || hasDefrag y
  hasDefrag (Count x y)     = hasDefrag y
  hasDefrag (Select x y)    = hasDefrag y
  hasDefrag (Crypt x y z)   = hasDefrag z
  hasDefrag (Decrypt x y z) = hasDefrag z
  hasDefrag (Frag x y)      = hasDefrag y
  hasDefrag (Defrag x y)    = True
  hasDefrag (Rel x)         = False
  hasDefrag (Hole_ x)       = False

  ||| Translates a Privy predicate into a C2QL predicate.
  predToC2QL : Pred e e' -> C2QLPred
  predToC2QL (AND x y)    = AND (predToC2QL x) (predToC2QL y)
  predToC2QL (OR x y)     = OR (predToC2QL x) (predToC2QL y)
  predToC2QL (Like a pat) = Like a pat
  predToC2QL (NextWeek a) = NextWeek a
  predToC2QL (Equal a v)  = Equal a v

  ||| Translates a Privy Query into a C2QL term.
  queryToC2QL : Query Δ -> C2QL -> C2QL
  queryToC2QL (Project δ q)       c2ql = Project δ (queryToC2QL q c2ql)
  queryToC2QL (Count δ q)         c2ql = Count δ (queryToC2QL q c2ql)
  queryToC2QL (Select p q)        c2ql = Select (predToC2QL p)
                                                (queryToC2QL q c2ql)
  queryToC2QL (Decrypt a d {c} q) c2ql = Decrypt a c (queryToC2QL q c2ql)
  queryToC2QL (Var_ δ)            c2ql = c2ql
  -- XXX: Go afeter the c2ql.defrag and continue there. This is not
  -- an issue for our examples.
  -- queryToC2QL (Defrag q1 q2)      c2ql = ?todoHandleFragCase
  -- TODO: Not supported! Sorry Bro!
  -- queryToC2QL (Product x y) c2ql = ?queryToC2QLContinue_rhs_2
  -- queryToC2QL (NJoin x y) c2ql = ?queryToC2QLContinue_rhs_3
  queryToC2QL q                   c2ql = c2ql

  ||| Translates a Privy term into a C2QL one.
  |||
  ||| @c2ql The initial C2QL term (in general, the relation `Rel`)
  privyToC2QL : Privy e e' Δ -> (c2ql : C2QL) -> UID C2QL
  privyToC2QL (Crypt a c) c2ql             = pure $ Crypt a c c2ql
  privyToC2QL (Frag δ') c2ql {e} with (hasDefrag c2ql)
    privyToC2QL (Frag δ') c2ql {e} | False =
      let fragId    = pred $ length e
          holeLeft  = Hole_ fragId
          holeRight = Hole_ (S fragId)
      in pure $ Defrag (holeLeft, holeRight) $ Frag δ' $ c2ql
    privyToC2QL (Frag δ') c2ql {e} | True  =
      let fragId     = pred $ length e
          holeLeft   = Hole_ fragId
          holeRight  = Hole_ (S fragId)
      in do
      let oldFrag = Hole_ !freshId
      let filler  = Defrag (holeLeft, holeRight) $ Frag δ' $ oldFrag
      pure $ c2qlFillHole c2ql holeLeft filler
  privyToC2QL (Query fId {env} kq) c2ql with (hasDefrag c2ql)
    privyToC2QL (Query fId {env} kq) c2ql | False =
      let query = kq $ Var_ (index fId env) in
      pure $ queryToC2QL query c2ql
    privyToC2QL (Query fId {env} kq) c2ql | True  =
      let query   = kq $ Var_ (index fId env)
          hole    = Hole_ (finToNat fId)
          oldFrag = Hole_ !freshId
          filler  = queryToC2QL query oldFrag
      in pure $ c2qlFillHole c2ql hole filler
  privyToC2QL ((>>=) p {δ} kp) c2ql        = do
    c2ql' <- privyToC2QL p c2ql
    let p' = kp $ Var_ δ
    privyToC2QL p' c2ql'
  privyToC2QL (Return p) c2ql              =
    pure $ queryToC2QL p c2ql
}


-- Tests

qaddr : C2QL -> C2QL
qaddr = Select (Like N "C*") .
        Decrypt N AES .
        Defrag (Project [Id] $ Hole_ 0, Project [N,A,Id] $ Hole_ 1) .
        Frag [D] . Crypt N AES

qmeet : C2QL -> C2QL
qmeet = Defrag (Count [D] $ Project [D,Id]
                          $ Select (NextWeek D)
                          $ Hole_ 0,
               Project [Id] $ Select (
                            AND (Equal A "Bureau")
                                (Equal N_AES "gTR7Y0kmcUCCK8f97EaLBQ=="))
                            $ Hole_ 1) .
               Frag [D] . Crypt N AES

qaddrC2QL : C2QL
qaddrC2QL = runPure $ toC2QL qaddr

qmeetC2QL : C2QL
qmeetC2QL = runPure $ toC2QL qmeet

qaddrC2QL' : C2QL
qaddrC2QL' = runPure $ toC2QL (do specCryptFrag ; qaddr')

qmeetC2QL' : C2QL
qmeetC2QL' = runPure $ toC2QL (do specCryptFrag ; qmeet')

test : IO ()
test = do putStrLn "------ Privy → C2QL/Unsafe"
          putStr "[adresses] = "
          printLn $ qaddrC2QL
          putStr "#rendezvous = "
          printLn $ qmeetC2QL
          putStrLn "------ Privy → C2QL"
          putStr "[adresses] = "
          printLn $ qaddrC2QL'
          putStr "#rendezvous = "
          printLn $ qmeetC2QL'

-- Local Variables:
-- eval: (setq idris-interpreter-path (expand-file-name "./linkIdris11"))
-- idris-load-packages: ("effects")
-- End:
