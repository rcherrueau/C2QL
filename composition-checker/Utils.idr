module Utils

import public Effects
import public Effect.State
import public Data.Vect

%default total
%access public export


||| Monad that computes an unique identifier.
UID : Type -> Type
UID ty = SimpleEff.Eff ty [STATE Nat]

||| Gets the next fresh identifier.
freshId : UID Nat
freshId = do id <- get
             update S
             pure id

||| Increases the fresh identifier counter after the value `k`.
incrAfter : Nat -> UID ()
incrAfter k = update (max (S k))

||| Resets the UID.
resetId : UID ()
resetId = update (const Z)

||| Lifts alternative `or' (<|>) into UID.
(<|>) : Alternative f => UID (f a) -> UID (f a) -> UID (f a)
(<|>) uid uid' = do a  <- uid
                    a' <- uid'
                    pure $ a <|> a'

||| Makes a fresh string symbol from the UID monad
mkSym : String -> UID String
mkSym s = (\id => s ++ (show id)) <$> freshId


||| A DataType to identify the place of the computation.
data Place = Frag Nat | App | Client | Bot

Eq Place where
  (Frag n) == (Frag m) = n == m
  App      == App      = True
  Client   == Client   = True
  Bot      == Bot      = True
  _        == _        = False

Show Place where
  show (Frag k) = "Frag " ++ show k
  show App      = "App"
  show Client   = "Client"
  show Bot      = "Bot"



||| Monad that stores the place of the computation
At : Type -> Type
At ty = SimpleEff.Eff ty [STATE Place]

||| Returns `true` if the current place is one of `ps`, `false`
||| otherwise.
ifPlace : (ps : List Place) -> (true : At a) -> (false : At a) -> At a
ifPlace ps true false = do
  p <- get
  if elem p ps then true else false


RelCtx : Type -> Type
RelCtx ty = SimpleEff.Eff ty [STATE (List String)]

push : String -> RelCtx ()
push s = update ((::) s)

pop : RelCtx String
pop = do qs <- get
         put (tail' qs)
         pure (head' qs)
  where
  head' []        = "_"
  head' (x :: xs) = x
  tail' []        = []
  tail' (x :: xs) = xs


namespace list
  sequence : List (EffM m a es (const es)) -> EffM m (List a) es (const es)
  sequence []        = pure []
  sequence (x :: xs) = pure $ !x :: !(sequence xs)

namespace vect
  sequence : Vect n (EffM m a es (const es)) -> EffM m (Vect n a) es (const es)
  sequence []        = pure []
  sequence (x :: xs) = pure $ !x :: !(sequence xs)

-- Local Variables:
-- eval: (setq idris-interpreter-path (expand-file-name "./linkIdris11"))
-- idris-load-packages: ("effects")
-- End:
