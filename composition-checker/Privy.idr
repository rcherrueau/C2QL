module Privy

import public Data.List
import public Data.Vect
import public Data.So

%default total
%access public export


namespace schema
  ||| Universe for cryptographic's types
  data CryptTy = AES -- | ElGamal | RSA | ...

  -- This should use idris-crypto
  -- see, https://github.com/idris-hackers/idris-crypto
  interpCryptTy : CryptTy -> Type -> Type
  interpCryptTy AES t = String


  ||| Universe for attribute's types
  data Ty = NAT | BOOL | TEXT | DATE | CRYPT CryptTy Ty

  interpTy : Ty -> Type
  interpTy NAT         = Nat
  interpTy BOOL        = Bool
  interpTy TEXT        = String
  interpTy DATE        = String
  interpTy (CRYPT c t) = interpCryptTy c (interpTy t)

  ||| An attribute is a name and a type.
  |||
  ||| Example: `the Attribute ("Name", TEXT)`
  Attribute : Type
  Attribute = (String, Ty)

  ||| A schema is a list of attribute.
  |||
  ||| Example: `the Schema [("Date", DATE),("Name", TEXT),("Address",TEXT)]`
  Schema : Type
  Schema = List Attribute

  ------------------------------------------------------- Schema utils
  Eq CryptTy where
    AES == AES = True
    _   == _   = False

  Eq Ty where
    NAT           == NAT            = True
    BOOL          == BOOL           = True
    TEXT          == TEXT           = True
    DATE          == DATE           = True
    (CRYPT AES x) == (CRYPT AES y)  = x == y
    _             == _              = False

  [attr] Show Attribute where
    show (a, _) = a

  [sch] Show Schema where
    show as = let f = Foldable.concat . intersperse ", " . map (show@{attr})
              in "[" ++ (f as) ++ "]"

  ||| Specific attribute for the indexing of fragments.
  Id : Attribute
  Id = ("Id", NAT)

  ||| Specific attribute that contains the result of a `count`.
  Cnt : Attribute
  Cnt = ("Count", NAT)

  ||| Tests if one schema is included in another.
  includes : Schema -> Schema -> Bool
  includes xs ys = all (flip elem ys) xs

  ||| Predicate that one schema is included in antoher.
  |||
  ||| This one is better than the So proof.
  data Inc : (xs : Schema) -> (ys : Schema) -> Type where
    ||| A proof that x ∈ ys ⇒ [x] ⊆ ys
    |||
    ||| Example: `the (Inc [("Bar",NAT)] [("Foo",TEXT),("Bar",NAT)]) Stop`
    Stop : {auto p : Elem x ys} -> Inc [x] ys
    ||| A proof that xs ⊆ ys ∧ x ∈ ys ⇒ (x :: xs) ⊆ ys.
    |||
    ||| Example: `the (Inc [("Foo",TEXT),("Bar",NAT)] [("Foo",TEXT),("Bar",NAT)]) (Pop Stop)`
    Pop  : Inc xs ys -> {auto p : Elem x ys} -> Inc (x :: xs) ys


-- Interfaces

||| The Equal interface defines over which Ty the developer can
||| perform an equality test.
interface Equal (ty : Ty) where

-- Every based type can perform an equality test
implementation Equal NAT where
implementation Equal BOOL where
implementation Equal TEXT where
implementation Equal DATE where

--- For encrypted value, the equality test is allowed on `AES` only
implementation Equal (CRYPT AES ty) where

-- Code sample for the Like interface with a bloom filter
-- LikeTerm : Type
-- LikeTerm = String

-- interface Like (ty : Ty) where
--   mkLikeTerm : (attrName : String) -> (v : String) -> LikeTerm

-- implementation Privy.Like TEXT where
--   mkLikeTerm x y = x ++ " LIKE " ++ y

-- implementation Privy.Like (CRYPT AES ty) where
--   mkLikeTerm x y = x ++ " BLOOM_FILTER_LIKE " ++ y

implementation Show CryptTy where
    show AES = "AES"


-- The EDSL of Relational Algebra
using (Δ : Schema, Δ' : Schema, δ : Schema, δ' : Schema,
       Δs : Vect n Schema,
       env : Env n , env' : Env m , env'' : Env k) {

Key : Type
Key = String

||| ADT that contains information for the decryption of something of
||| type `CryptTy`.
data Decrypt : CryptTy -> Type where
  ||| AES decryption requieres a key.
  AES    : Key -> Decrypt schema.AES
  ||| AES-CBC requires a key and an initialization vector.
  AESCBC : Key -> Vect 16 Bits8 -> Decrypt schema.AES

namespace query

  ||| ADT for the predicate of a σ in the relational algebra.
  |||
  ||| @ Δ  the schema over which this predicate is tested.
  ||| @ ty the attribute type produces by this predicate.
  |||
  ||| You should use the sugar accessor rather than this constructor.
  ||| Inside the repl `:browse Privy.sugar`
  data Pred : (Δ : Schema) -> (ty : Ty) -> Type where
    ||| Logical AND
    AND      : Pred Δ BOOL -> Pred Δ BOOL -> Pred Δ BOOL
    ||| Logical OR
    OR       : Pred Δ BOOL -> Pred Δ BOOL -> Pred Δ BOOL
    ||| Test that values of `a` contains `pat`.
    |||
    ||| @ p proof that `a` is an attribute of `Δ`.
    Like     : (a : Attribute) -> (pat : String) ->
               {auto p : Elem a Δ} ->
               -- Like (snd a) => -- to add the like interface
               Pred Δ BOOL
    ||| Test that values of `a` are a next week date.
    |||
    ||| @ p1 proof that `a` is a `DATE`.
    ||| @ p2 proof that `a` is an attribute of `Δ`.
    NextWeek : (a : Attribute) ->
               {default Refl p1 : DATE = (snd a)} ->
               {auto p2 : Elem a Δ} ->
               Pred Δ BOOL
    ||| Test that values of `a` are equals to `v`.
    |||
    ||| @ v a value with the idris type of `a`.
    ||| @ p proof that `a` is an attribute of `Δ`.
    Equal    : (a : Attribute) -> (v : interpTy (snd a)) ->
               {auto p : Elem a Δ} ->
               Equal (snd a) => -- Note the presence of our interface
               Eq (interpTy (snd a))   => -- For debugging only,
               Show (interpTy (snd a)) => -- not required
               Pred Δ BOOL

  mutual
    -- TODO: remove me. to only export definition. Then give access to
    -- constructor through public function, but do not expose `Var_`
    -- that is for internal construction only.

    ||| ADT for a query in the relational algebra.
    |||
    ||| @ Δ the schema of values produces by this query.
    |||
    ||| You should use the sugar accessor rather than this
    ||| constructor. Inside the repl `:browse Privy.sugar`
    data Query : (Δ : Schema) -> Type where
      ||| π term.
      |||
      ||| @ p proof that `δ` ⊆ `Δ`
      |||
      ||| Describes the projection of `δ` over `Δ`
      Project : (δ : Schema) -> Query Δ -> {auto p : Inc δ Δ} ->
                Query δ
      Product : Query Δ -> Query Δ' -> Query (Δ ++ Δ')
      NJoin   : Query Δ -> Query Δ' ->
                {default Oh p : So (hasAny Δ Δ')} ->
                Query (nub (Δ ++ Δ'))
      ||| count term.
      |||
      ||| @ p proof that `δ` ⊆ `Δ`
      |||
      ||| Describes a group on `δ` and counts the number of line in
      ||| each group.
      Count   : (δ : Schema) -> Query Δ -> {auto p : Inc δ Δ} ->
                Query (δ ++ [Cnt])
      ||| σ term.
      |||
      ||| Specifies a filter on a specific predicate `p`.
      Select  : (p : Pred Δ BOOL) -> Query Δ -> Query Δ
      ||| decrypt term.
      |||
      ||| @ p1 proof that value of `a` are encrypted with `c`.
      ||| @ p2 proof that `a` ∈ `Δ`
      |||
      ||| Describes the decryption of values of `a` using information
      ||| in ADT `d`.
      Decrypt : (a : Attribute) -> (d : Decrypt c) ->
                {default Refl p1 : (CRYPT c t) = (snd a)} ->
                {auto p2 : Elem a Δ} ->
                Query Δ -> Query (replaceOn a (fst a, t) Δ)
      ||| defrag term.
      |||
      -- ||| @ p proof that this term is ok with the count law. Not
      -- ||| needed thanks to the transformation in Proverif. The
      -- ||| reader can remove commentary related to this proof to
      -- ||| test it. However, the read has to replace all occurrence
      -- ||| of `UniqueType` with `Type`.
      |||
      ||| Describes the defragmentation of values of `q1` and `q2`
      ||| (this removes `Id`).
      Defrag : (q1 : Query δ) -> (q2 : Query δ') ->
               -- {auto p : So (countLaw q1 q2)} ->
               Query (delete Id (nub (δ ++ δ')))

      ||| Do not use this, for transformation only.
      Var_  : (Δ : Schema) -> Query Δ

    -- ||| Tests the count law.
    -- countLaw : Query δ -> Query δ' -> Bool
    -- countLaw q1 q2 = not (bothCnt q1 q2)
    --                  && followLaw q1 q2
    --                  && followLaw q2 q1
    --   where
    --   -- XXX: HACK : test that schema contains "Cnt" -- Ok if nothing
    --   -- comes after the Count function (that is the expected
    --   -- behavior). I should go with a proof on the term rather than
    --   -- an `So` one.
    --   hasCnt : Query δ -> Bool
    --   hasCnt _ {δ} = elem Cnt δ

    --   bothCnt : Query δ -> Query δ' -> Bool
    --   bothCnt q1 q2 = hasCnt q1 && hasCnt q2

    --   followLaw : Query s -> Query s' -> Bool
    --   followLaw q _ {s'} with (hasCnt q)
    --     followLaw q _ {s'} | False = True
    --     followLaw q _ {s'} | True  = s' == [Id]


-- The EDSL for CCQL
namespace privy
  ||| Type of the environnement.
  |||
  ||| @ n the size of the environnement. Z means 1 db, (S Z) means 2
  ||| frag and so on.
  Env : (n : Nat) -> Type
  Env n = Vect (S n) Schema

  ||| Returns true if `a` exists in the environnement.
  isInEnv : (a : Attribute) -> (env : Env n) -> Bool
  isInEnv a env = any (elem a) env

  ||| Predicate that ensures that a ∈ env.
  |||
  ||| Use this rather than `So` proof on `isInEnv`.
  data EnvElem : (a : Attribute) -> (env : Env n) -> Type where
    Here  : {auto p : Elem a (head env)} -> EnvElem a env
    There : EnvElem a env -> EnvElem a (e :: env)

  ||| Sets attribute `a` with cryptographic schema `c` in `env`.
  |||
  ||| @ p proof that `a` ∈ `env`.
  cryptEnv : (c : CryptTy) -> (a : Attribute) -> (env : Env n) ->
             {auto p : EnvElem a env} -> Env n
  cryptEnv c a env       {p = Here}      =
    let Δ    = head env
        Δenc = replaceOn a (fst a, CRYPT c (snd a)) Δ
    in replaceAt FZ Δenc env
  cryptEnv c a (e :: env) {p = (There p')} =
    e :: (cryptEnv c a env {p=p'})

  ||| Fragments the environnement in the last fragment.
  |||
  ||| @ p proof that `δ` ⊆ `(last env)`
  fragEnv : (δ : Schema) -> (env : Env n) ->
            {auto p : Inc δ (last env)} ->
            Env (S n)
  fragEnv δ env {n} = let Δs  = init env
                          Δ   = last env
                          Δl  = (intersect δ Δ) ++ [Id]
                          Δr  = nub ((Δ \\ δ) ++ [Id])
                          res = Δs ++ [Δl,Δr]
                      in rewrite sym (plusTwoSucSuc n) in res
    where
    -- a gentle proof
    plusTwoSucSuc : (n : Nat) -> n + 2 = S (S n)
    plusTwoSucSuc Z     = Refl
    plusTwoSucSuc (S k) = let inductHypo = plusTwoSucSuc k
                          in cong inductHypo {f=S}

  ||| ADT for the EDSL of C2QL.
  |||
  ||| @ env0 the state of the environnement before the query.
  ||| @ env1 the state of the environnement after the query.
  ||| @ Δ the schema of values produces by this query.
  |||
  ||| You should use the sugar accessor rather than this
  ||| constructor. Inside the repl `:browse Privy.sugar`
  -- data Privy : (env0 : Env n) -> (env1 : Env m) -> (Δ : Schema) -> UniqueType where
  data Privy : (env0 : Env n) -> (env1 : Env m) -> (Δ : Schema) -> Type where
    ||| crypt term.
    |||
    ||| @ p proof that `a` is in `env`.
    |||
    ||| Specifies to encrypt attribute's values in the environnement.
    Crypt : (a : Attribute) -> (c : CryptTy) ->
            {auto p : EnvElem a env} -> Privy env (cryptEnv c a env) []
    ||| frag term.
    |||
    ||| @ p proof that `δ` ⊆ `(last env)`
    |||
    ||| Specifies to fragment the last frag of the environnement.
    Frag : (δ : Schema) ->
           {auto p : Inc δ (last env)} ->
           Privy env (fragEnv δ env) []
    -- Query : (q : Query δ -> Query δ') ->
    --         {default Oh p : So (includes δ Δ)} ->
    --         -- q should take a Δ'' that is a subset of Δ si j'arrive à
    --         -- faire ça => j'ai la réutilisation.
    --         Privy (MkEnv [Δ]) (MkEnv [Δ]) δ'
    -- Move  : (env' : Env n) -> Privy _ env' []
    ||| query term.
    |||
    ||| Decribes a query on the `fId` fragment.
    Query : {env : Env n} ->
            (fId : Fin (S n)) -> (q : Query (index fId env) -> Query Δ') ->
             Privy env env Δ'
    ||| bind term.
    (>>=) : Privy  env env' δ ->
            (Query δ -> Privy env' env'' δ') ->
            Privy env env'' δ'
    ||| return term.
    Return : Query δ -> Privy env env δ

--   -- Syntaxe
--   Query : (q : Query δ -> Query δ') ->
--           {default Oh p : So (includes δ Δ)} ->
--           -- q should take a Δ'' that is a subset of Δ si j'arrive à
--           -- faire ça => j'ai la réutilisation.
--           Privy (MkEnv [Δ]) (MkEnv [Δ]) δ'
--   Query = Query


namespace sugar
  ---------------------------------------------------- Predicate sugar
  -- export
  like : (a : Attribute) -> String -> {auto p : Elem a Δ} ->
         Pred Δ BOOL
  like = Like

  -- export
  (&&) : Pred Δ BOOL -> Pred Δ BOOL -> Pred Δ BOOL
  (&&) = AND

  -- export
  (||) : Pred Δ BOOL -> Pred Δ BOOL -> Pred Δ BOOL
  (||) = OR

  -- export
  (==) : (a : Attribute) -> (v : interpTy (snd a)) ->
         {auto p : Elem a Δ} ->
         Equal (snd a) =>
         Eq (interpTy (snd a))   =>
         Show (interpTy (snd a)) =>
         Pred Δ BOOL
  (==) = Equal

  -- export
  nextWeek : (a : Attribute) -> {default Refl p1 : DATE = (snd a)} ->
             {auto p2 : Elem a Δ} -> Pred Δ BOOL
  nextWeek = NextWeek

  -------------------------------------------------------- Query sugar
  -- export
  π : (δ : Schema) -> Query Δ -> {auto p :Inc δ Δ} -> Query δ
  π = Project

  -- export
  count : (δ : Schema) -> Query Δ -> {auto p : Inc δ Δ} ->
          Query (δ ++ [Cnt])
  count = Count

  -- export
  σ : Pred Δ BOOL -> Query Δ' ->
      -- XXX: Instruct the unifyier to infer the Δ from Δ'
      {default Refl p : Δ = Δ'} -> Query Δ
  σ f q {p=Refl} = Select f q

  -- export
  decrypt : (a : Attribute) -> (d : Decrypt c) ->
            {default Refl p1 : (CRYPT c t) = (snd a)} ->
            {auto p2 : Elem a Δ} ->
            Query Δ' ->
            {default Refl p3 : Δ = Δ'} ->
            Query (replaceOn a (fst a, t) Δ)
  decrypt a d q {p1} {p2} {p3=Refl} = Decrypt a d q {p1=p1} {p2=p2}

  -- export
  defrag : (q1 : Query δ) -> (q2 : Query δ') ->
           -- {auto p : So (countLaw q1 q2)} ->
           Query (delete Id (nub (δ ++ δ')))
  defrag = Defrag

  -------------------------------------------------------- Privy sugar
  -- export
  crypt : (a : Attribute) -> (c : CryptTy) ->
          {auto p : EnvElem a env} -> Privy env (cryptEnv c a env) []
  crypt = Crypt

  frag : (δ : Schema) -> {auto p : Inc δ (last env)} ->
         Privy env (fragEnv δ env) []
  frag = Frag

  query : {env : Env n} ->
          (fId : Fin (S n)) -> (q : Query (index fId env) -> Query Δ') ->
          Privy env env Δ'
  query = Query

  return : Query δ -> Privy env env δ
  return = Return

  data App : (env : Env n) -> Type where
    Nil  : App env
    (::) : Privy _ env _ -> App env -> App env
}


D : Attribute
D = ("Date", DATE)

N : Attribute
N = ("Nom", TEXT)

A : Attribute
A = ("Adresse", TEXT)

RendezVous : Schema
RendezVous = [D,N,A] -- D :: N :: A :: Nil

N_AES : Attribute
N_AES = ("Nom", CRYPT AES TEXT)

RendezVousEnv : Env 0
RendezVousEnv = [RendezVous]

SafeRendezVousEnv : Env 1
SafeRendezVousEnv = [[D,Id], [N_AES,A,Id]]

SafeRendezVousEnv' : Env 1
SafeRendezVousEnv' = fragEnv [D] $ cryptEnv AES N RendezVousEnv

sameEnv : SafeRendezVousEnv = SafeRendezVousEnv'
sameEnv = Refl

-- -- ill-typed:
-- FalseEnv1 : Env 3
-- FalseEnv1 = fragEnv [D] $ fragEnv [D] RendezVousEnv

-- -- ill-typed:
-- FalseEnv2 : Env 2
-- FalseEnv2 = cryptEnv 0 AES N $ fragEnv [D] RendezVousEnv


-- The bottom Query type
Bot : List _
Bot = []

specCryptFrag : Privy RendezVousEnv SafeRendezVousEnv Bot
specCryptFrag = do crypt N AES ; frag [D]

specFragCrypt : Privy RendezVousEnv SafeRendezVousEnv Bot
specFragCrypt = do frag [D] ; crypt N AES

specFragDA : Privy SafeRendezVousEnv [[D,Id], [A,Id], [N_AES,Id]] Bot
specFragDA = frag [A]

-- -- ill-typed:
-- falseSpecFragLeft: Privy RendezVousEnv _ Bot
-- falseSpecFragLeft = do frag [D,A] ; frag [D]

-- -- ill-typed:
-- falseSpecCrypt : Privy RendezVousEnv _ Bot
-- falseSpecCrypt = crypt ("Foo", TEXT) AES

-- -- ill-typed:
-- falseSpecFragDA : Privy SafeRendezVousEnv _ Bot
-- falseSpecFragDA = frag [D,A]


qDate : Privy SafeRendezVousEnv SafeRendezVousEnv [D]
qDate = query 0 (\q => π [D] q)

-- -- ill-typed:
-- qfalseFragAccess : Privy SafeRendezVousEnv SafeRendezVousEnv ?theType
-- qfalseFragAccess = query 2 id

-- -- ill-typed:
-- qFalseΠ : Privy SafeRendezVousEnv SafeRendezVousEnv ?theType
-- qFalseΠ = query 0 (\q => π [N] q)

-- On a local env
qaddr : Privy RendezVousEnv RendezVousEnv [N,A]
qaddr = query 0 (\q => σ (N `like` "C*") $ π [N,A] $ q)

qmeet : Privy RendezVousEnv RendezVousEnv [D,Cnt]
qmeet = query 0 (\q => count [D] $
                       π [D] $
                       σ (nextWeek D && A == "Bureau" && N ==  "Bob") q)

qcomp : Privy RendezVousEnv RendezVousEnv [N,A,D,Cnt]
qcomp = qaddr  >>= \q1 =>
        qmeet  >>= \q2 =>
        return (Product q1 q2)


-- On a safe env
qaddr' : Privy SafeRendezVousEnv SafeRendezVousEnv [N,A]
qaddr' = do
  rl <- query 0 (\q => π [Id] q)
  rr <- query 1 (\q => π [Id, N_AES, A] q)
  return $ σ (N `like` "C*") $ decrypt N_AES (AES "key") $ defrag rl rr

qmeet' : Privy SafeRendezVousEnv SafeRendezVousEnv [D,Cnt]
qmeet' = do
  rl <- query 0 (\q => count [D,Id] $ π [D,Id] $ σ (nextWeek D) q)
  rr <- query 1 (\q => π [Id] $
                       σ (A == "Bureau" &&
                          N_AES == "gTR7Y0kmcUCCK8f97EaLBQ==") q)
  return $ defrag rl rr

-- -- ill-typed:
-- qmeet'' : Privy SafeRendezVousEnv SafeRendezVousEnv _
-- qmeet'' = do
--   rl <- query 0 (\q => count [D,Id] $ π [D,Id] $ σ (nextWeek D) q)
--   rr <- query 1 (\q => π [A,Id] $
--                        σ (A == "Bureau" &&
--                           N_AES == "gTR7Y0kmcUCCK8f97EaLBQ==") q)
--   return defrag rl rr -- So false


calendar : App SafeRendezVousEnv
calendar = [qaddr', qmeet']

-- Local Variables:
-- eval: (setq idris-interpreter-path (expand-file-name "./linkIdris11"))
-- End:
