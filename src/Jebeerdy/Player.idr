module Jebeerdy.Player

import Data.SortedMap
import Data.SortedSet
import JSON.Derive

%language ElabReflection
%default total


||| An integer which represents a player.
|||
||| A player id is an integer from 0 to (1 - nplayers) of players,
||| which in Idris is called `Fin`.
public export
0 PlayerID : (0 n : Nat) -> Type
PlayerID n = Fin n

||| A player's name together with their score.
public export
record Player where
  constructor MkPlayer
  name  : String
  score : Integer
%runElab derive "Player" [Show, Eq, Ord, FromJSON, ToJSON]

||| A set of players ranked in the order in which they hit the buzzer.
public export
0 PlayerQueue : Nat -> Type
PlayerQueue np = SortedMap (PlayerID np) Nat

||| Get the player who buzzed in first
export
(.firstPlayer) : PlayerQueue np -> Maybe (PlayerID np)
(.firstPlayer) buzzed = map fst $ head' $ sortBy buzzerTime $ toList buzzed
  where
    buzzerTime : (PlayerID np, Nat) -> (PlayerID np, Nat) -> Ordering
    buzzerTime (p1, t1) (p2, t2) = compare t1 t2

||| Remove the player who buzzed in first, making the next player the 'first'.
export
(.next) : PlayerQueue np -> PlayerQueue np
(.next) buzzed = case buzzed.firstPlayer of
  Nothing => empty
  Just p => delete p buzzed

export
updateScore : Integer -> Player -> Player
updateScore value = {score $= (+ value)}
