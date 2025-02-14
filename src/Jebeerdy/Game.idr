module Jebeerdy.Game


import Data.List
import Data.Vect
import Data.SortedMap
import Data.SortedSet
import JSON.Derive


%language ElabReflection
%default total


||| A Cell is an Answer and its question
|||
||| For more complex game variations, we could expand on this type.
|||
||| Note that the answers are not stored in the cell. Cells are immutable.
public export
record Cell where
  constructor MkCell
  clue : String
  question : String
%runElab derive "Cell" [Show, Eq, Ord, FromJSON, ToJSON]

||| A complete game board.
|||
||| This contains the cell grid, plus the column and value
||| annotations. Like Cell, it is also read-only, plus the final
||| round.
export
record Board (rows : Nat) (cols : Nat) where
  constructor MkBoard
  name       : String
  categories : Vect cols String
  values     : Vect rows Nat
  cells      : Vect cols (Vect rows Cell)
  final      : Cell
%runElab deriveIndexed "Board" [Show, Eq, Ord, {- FromJSON,-} ToJSON]

||| A player's name together with their score.
export
record Player where
  constructor MkPlayer
  name  : String
  score : Integer
%runElab derive "Player" [Show, Eq, Ord, FromJSON, ToJSON]

||| Get a cell by row and column
(.get) : Fin rows -> Fin cols -> Board rows cols -> Cell
-- Dependent types here make it impossible to confuse rows and cols here.
(.get) i j self = index i $ index j self.cells

||| An integer which represents a player.
|||
||| A player id is an integer from 0 to (1 - nplayers) of players,
||| which in Idris is called `Fin`.
0 PlayerID : (0 n : Nat) -> Type
PlayerID n = Fin n

||| A reference to a cell position
0 CellID : (0 rows : Nat) -> (0 cols : Nat) -> Type
CellID rows cols = (Fin rows, Fin cols)

||| A set of players ranked in the order in which they hit the buzzer.
0 PlayerQueue : Nat -> Type
PlayerQueue np = SortedMap (PlayerID np) Nat

||| Get the player who buzzed in first
(.firstPlayer) : PlayerQueue np -> Maybe (PlayerID np)
(.firstPlayer) buzzed = map fst $ head' $ sortBy buzzerTime $ toList buzzed
  where
    buzzerTime : (PlayerID np, Nat) -> (PlayerID np, Nat) -> Ordering
    buzzerTime (p1, t1) (p2, t2) = compare t1 t2

||| Remove the player who buzzed in first, making the next player the 'first'.
(.next) : PlayerQueue np -> PlayerQueue np
(.next) buzzed = case buzzed.firstPlayer of
  Nothing => empty
  Just p => delete p buzzed

||| These are the actions which affect the game state.
export
data Action : (rows : Nat) -> (cols : Nat) -> (np : Nat) -> Type where
  ChoosePlayer : PlayerID n -> Action rows cols n
  ChooseCell   : CellID rows cols -> Action rows cols np
  Advance      : Action rows cols np
  BuzzIn       : PlayerID n -> Nat -> Action rows cols n
  Score        : Bool -> Action rows cols np

||| The current state of play.
data State : Nat -> Nat -> Nat -> Type where
  AwaitPlayer   : State rows cols np
  AwaitCell     : PlayerID np -> State rows cols np
  ReadQuestion  : CellID rows cols -> State rows cols np
  AwaitBuzzer   : PlayerQueue np -> CellID rows cols -> State rows cols np
  AwaitScore    : PlayerQueue np -> CellID rows cols -> State rows cols np
  Done          : State rows cols np

||| The entire game state, information common to all game states.
export
record Game (rows : Nat) (cols : Nat) (np : Nat) where
  constructor MkGame
  board   : Board rows cols
  players : Vect np Player
  free    : SortedSet (CellID rows cols)
  error   : Maybe String
  state   : State rows cols np

||| The current player, if the game can be said to have one.
(.playerID) : Game rows cols np -> Maybe (PlayerID np)
(.playerID) game = case game.state of
  AwaitPlayer            => Nothing
  (AwaitCell id)         => Just id
  (ReadQuestion _)       => Nothing
  (AwaitBuzzer buzzed _) => buzzed.firstPlayer
  (AwaitScore  buzzed _) => buzzed.firstPlayer
  Done                   => Nothing

||| Get the current player's name, if it has one.
(.player) : Game rows cols np -> Maybe Player
(.player) game = pure $ index !game.playerID game.players

||| Get the monetary value of the given cell
(.cellValue) : Game rows cols np -> CellID rows cols -> Nat
(.cellValue) self cell = index (fst cell) self.board.values

||| Update the given player's score by the given amount
(.adjustScore)
  :  Game rows cols np
  -> PlayerID np
  -> Bool
  -> CellID rows cols
  -> Game rows cols np
(.adjustScore) self id correct cell =
  let value : Integer = cast $ self.cellValue cell
  in case correct of
    True  => {players $= updateAt id (updateScore value)} self
    False => {players $= updateAt id (updateScore (-value))} self
where
  updateScore : Integer -> Player -> Player
  updateScore value = {score $= (+ value)}

||| Mark the given cell as having been played.
(.clearCell)
  :  Game rows cols np
  -> CellID rows cols
  -> Game rows cols np
(.clearCell) self cell = {free $= delete cell} self

||| True if all the cells have been cleared
(.done) : Game rows cols np -> Bool
(.done) self = self.free == empty

||| Start the turn with the given player
(.beginTurn) : Game rows cols np -> PlayerID np -> Game rows cols np
(.beginTurn) self player = {state := AwaitCell player} self

||| Record the player's cell choice
(.chooseCell) : Game rows cols np -> CellID rows cols -> Game rows cols np
(.chooseCell) self cell = {state := ReadQuestion cell} self

||| Wait for the players to buzz in
(.armBuzzers) : Game rows cols np -> CellID rows cols -> Game rows cols np
(.armBuzzers) self cell = {state := AwaitBuzzer empty cell} self

||| Clear the current cell, and reset the game state.
(.endTurn)
  :  Game rows cols np
  -> CellID rows cols
  -> Game rows cols np
(.endTurn) self cell = {
  free  $= delete cell,
  state := AwaitPlayer
} self

||| Record the player buzzing in at the given time.
(.buzzIn)
  :  Game rows cols np
  -> PlayerQueue np
  -> PlayerID np
  -> Nat
  -> CellID rows cols
  -> Game rows cols np
(.buzzIn) self pq player time cell = {
  state := AwaitBuzzer (insert player time pq) cell
} self

||| Advance to the next buzzed-in player.
(.nextPlayer)
  :  Game rows cols np
  -> PlayerQueue np
  -> CellID rows cols
  -> Game rows cols np
(.nextPlayer) self pq cell =
  let pq = pq.next
  in case (pq == empty) of
    True => self.endTurn cell
    False => {state := AwaitScore pq cell} self

||| Helper function
(.scorePlayer)
  :  Game rows cols np
  -> PlayerQueue np
  -> Bool
  -> CellID rows cols
  -> Game rows cols np
(.scorePlayer) self buzzed correct cell = case buzzed.firstPlayer of
  Nothing => self.endTurn cell
  Just p  => self.adjustScore p correct cell

||| Helper function to set error messages
(.error)
  :  Game rows cols np
  -> String
  -> Game rows cols np
(.error) self msg = {error := Just msg} self

||| The transition function for the game's state machine.
export
transition
  :  Game   rows cols np
  -> Action rows cols np
  -> Game   rows cols np
transition game = go game.state
  where
    ||| Main table of transitions.
    go
      :  State rows cols np
      -> Action rows cols np
      -> Game rows cols np
    go AwaitPlayer   (ChoosePlayer player) = game.beginTurn player
    go (AwaitCell _) (ChooseCell cell)     = game.chooseCell cell
    go (ReadQuestion   cell) Advance       = game.armBuzzers cell
    go (AwaitBuzzer pq cell) (BuzzIn id t) = game.buzzIn pq id t cell
    go (AwaitBuzzer pq cell) Advance       = {state := AwaitScore pq cell} game
    go (AwaitScore  pq cell) (Score c)     = game.scorePlayer pq c cell
    go Done _                              = game
    go _           _                       = game.error "Invalid Action"
