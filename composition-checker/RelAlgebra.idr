module RelAlgebra

-- Based On [OS08]
--
-- @InProceedings{OS08,
--   author =       {Nicolas Oury and Wouter Swierstra},
--   title =        {The power of Pi},
--   booktitle =    {Proceeding of the 13th {ACM} {SIGPLAN} international
--                   conference on Functional programming, {ICFP} 2008,
--                   Victoria, BC, Canada, September 20-28, 2008},
--   pages =        {39--50},
--   year =         2008,
--   url =          {http://doi.acm.org/10.1145/1411204.1411213},
--   doi =          {10.1145/1411204.1411213}
-- }

import Data.List
import Data.So

%default total
%access public export

-- Types for the Relational Algebra
namespace schema
  data Ty = NAT | BOOL | TEXT | DATE

  interpTy : Ty -> Type
  interpTy NAT  = Nat
  interpTy BOOL = Bool
  interpTy TEXT = String
  interpTy DATE = String

  Eq Ty where
    NAT  == NAT  = True
    BOOL == BOOL = True
    TEXT == TEXT = True
    DATE == DATE = True
    _    == _    = False

  Attribute : Type
  Attribute = (String, Ty)

  Schema : Type
  Schema = List Attribute

  -- Axiom: A schema is never empty.
  --
  -- We should go with our properer Schema construction, rather than a
  -- List to ensure that, but going with List takes the benefit of the
  -- List library.
  --
  -- Moreover, this is only useful for the next method that coerce a
  -- schema into a tuple.
  postulate nonEmpty : (δ : Schema) -> NonEmpty δ

  -- Makes a tuple from a schema
  sch2tuple : (δ : Schema) ->
              {default (nonEmpty δ) ok : NonEmpty δ} -> Type
  sch2tuple []                     {ok} = absurd ok
  sch2tuple [(_,t)]                {ok} = interpTy t
  sch2tuple ((_,t) :: s@(x :: xs)) {ok} = let tupleRest = sch2tuple s
                                              tupleVal  = interpTy t
                                          in Pair tupleVal tupleRest

  includes : Eq a => List a -> List a -> Bool
  includes xs ys = all (flip elem ys) xs

-- TODO: Handle the connection with the real world
namespace io
  -- TODO: Handle all information to connect to the database.
  data Handler : Schema -> Type where
    MkHandler : (url : String) -> (table : String) -> Handler s

  -- TODO: Error of the database.
  data DBError = BadSchema String String Schema | TimeOut

  -- TODO: This should:
  -- 1. Connect to the database using url
  -- 2. Ensures that table has the schema Δ
  -- 3. Returns the handlers with all necessary information to query
  --    the databases.
  connect : String -> String -> (Δ : Schema) ->
            IO (Either DBError (Handler Δ))
  connect url table Δ = return $ Right (MkHandler url table)

-- The EDSL of Relational Algebra
namespace query
  using (Δ : Schema, Δ' : Schema) {

  data Pred : Schema -> Ty -> Type where
    AND      : Pred Δ BOOL -> Pred Δ BOOL -> Pred Δ BOOL
    OR       : Pred Δ BOOL -> Pred Δ BOOL -> Pred Δ BOOL
    Like     : (a : Attribute) ->
               {auto p1 : TEXT = (snd a)} -> {auto p2 : Elem a Δ} ->
               String -> Pred Δ BOOL
    NextWeek : (a : Attribute) ->
               {auto p1 : DATE = (snd a)} -> {auto p2 : Elem a Δ} ->
               Pred Δ BOOL
    Equal    : (a : Attribute) -> (v : interpTy (snd a)) ->
               {auto p : Elem a Δ} ->
               Pred Δ BOOL

  data Query : Schema -> Type where
    Project : (δ : Schema) -> Query Δ ->
              {auto p : So (includes δ Δ)} ->
              Query δ
    Product : Query Δ -> Query Δ' -> Query (Δ ++ Δ')
    NJoin   : Query Δ -> Query Δ' ->
              {auto p : So (hasAny Δ Δ')} ->
              Query (nub (Δ ++ Δ'))
    Count   : (δ : Schema) -> Query Δ ->
              {auto p : So (includes δ Δ)} ->
              Query (δ ++ [("Count", NAT)])
    Select  : Pred Δ BOOL -> Query Δ -> Query Δ
    Unit    : Handler Δ ->  Query Δ

  -- Note: This should:
  -- 1. Compute a SQL query from the Query term
  -- 2. Query the database using the query handler
  -- 3. Returns the result
  query : Query Δ -> IO (List (sch2tuple Δ))
  query q = return Nil

  }

-- A better syntax for the EDSL
namespace qsyntax
  using (Δ: Schema, Δ': Schema) {

  (&&) : Pred Δ BOOL -> Pred Δ BOOL -> Pred Δ BOOL
  (&&) = AND

  (||) : Pred Δ BOOL -> Pred Δ BOOL -> Pred Δ BOOL
  (||) = OR

  π : (δ: Schema) -> Query Δ ->
      {auto p: So (includes δ Δ)} ->
      Query δ
  π = Project

  σ : Pred Δ BOOL -> Query Δ -> Query Δ
  σ = Select

  count : (δ: Schema) -> Query Δ ->
          {auto p: So (includes δ Δ)} ->
          Query (δ ++ [("Count", NAT)])
  count = Count

  unit : Handler Δ ->  Query Δ
  unit = Unit


  (==) : (a : Attribute) -> (v : interpTy (snd a)) ->
         {auto p : Elem a Δ} ->
         Pred Δ BOOL
  (==) = Equal

  }


-- Tests

-- Query with unknown schema
mchoose : (b : Bool) -> Maybe (So b)
mchoose b = either Just (const Nothing) (choose b)

qdynamic : {s,s': Schema} -> Handler s -> Maybe (Query s')
qdynamic h {s} {s'} = do
  -- Get the proof and do the request if any
  prf <- mchoose (includes s' s)
  return (π s' {p=prf} (Unit h))

-- Query with schema knows at compile time
D : Attribute
D = ("Date", DATE)

N : Attribute
N = ("Nom", TEXT)

A : Attribute
A = ("Adresse", TEXT)

RendezVous : Schema
RendezVous = [D,N,A] -- D :: N :: A :: Nil

qaddr : Handler RendezVous -> Query [N,A]
qaddr rdv = σ (N `Like` "C*") $ π [N,A] $ unit rdv

qmeet : Handler RendezVous -> Query [D,("Count", NAT)]
qmeet rdv = count [D] $ π [D] $
                        σ (NextWeek D && A == "Bureau" && N == "Bob") $
                        unit rdv

main : IO ()
main = do
  eh <- connect "pg://user:passwd@url:port" "RendezVous" RendezVous
  case eh of
    Left error => putStrLn "Erreur à la connexion"
    Right h =>
      do putStrLn "Requête [adresse] :"
         adresses <- query $ qaddr h
         putStrLn (show adresses)
         putStrLn "Requête #rendezvous :"
         nbRdv <- query $ qmeet h
         putStrLn (show nbRdv)


-- Some tests with elab meta-programming
l : Nat
l = ?l_rhs

---------- Proofs ----------
l_rhs = %runElab (do fill `(Z)
                     solve)

-- Local Variables:
-- eval: (setq idris-interpreter-path (expand-file-name "./linkIdris11"))
-- End:
