module Jebeerdy.Game

import Data.List
import Data.Vect
import Data.SortedMap
import Data.SortedSet
import Jebeerdy.Board
import Jebeerdy.Player
import JSON.Derive

%language ElabReflection
%default total


||| Games are configurable along these dimensions.
|||
||| It is used as a type parameter to to simplify dependent type
||| signatures.
|||
||| In other words, rather than have to pass `rows`, `cols`, `nplayers`
||| as explicit type parameters, we can just pass `p`.
public export
record Params where
  rows : Nat
  cols : Nat
  nplayers : Nat

||| Add CellID as an 'associated type' to `p`.
|||
||| I.e. we can write `p.CellID`, rather than `CellID p.rows p.cols`.
public export
0 (.CellID) : Params -> Type
(.CellID) p = CellID p.rows p.cols

||| Add PlayerID as an 'associated type' to `p`.
|||
||| I.e. we can write `p.PlayerID`, rather than `PlayerID p.nplayers`.
public export
0 (.PlayerID) : Params -> Type
(.PlayerID) p = PlayerID p.nplayers

||| The current state of play.
data State
  = AwaitPlayer
  | AwaitCell
  | ReadQuestion
  | AwaitBuzzer
  | AwaitScore
  | Done

||| Stores the current cell id and queue of buzzed-in players.
record Buzzer (p : Params) where
  constructor Buzz
  players : PlayerQueue p.nplayers
  cell    : p.CellID

||| Type of the game's state-dependent field.
0 StateData : State -> Params -> Type
StateData AwaitPlayer  p = ()
StateData AwaitCell    p = p.PlayerID
StateData ReadQuestion p = p.CellID
StateData AwaitBuzzer  p = Buzzer p
StateData AwaitScore   p = Buzzer p
StateData Done         p = p.PlayerID

||| The entire game state, information common to all game states.
export
record Game (state : State) (p : Params) where
  constructor MkGame
  board    : Board p.rows p.cols
  players  : Vect p.nplayers Player
  free     : SortedSet p.CellID
  forState : StateData state p

||| The current player, if the game can be said to have one.
(.playerID)
  : {state : State}
  -> Game state p
  -> Maybe p.PlayerID
(.playerID) self = case state of
  AwaitPlayer  => Nothing
  AwaitCell    => Just self.forState
  ReadQuestion => Nothing
  AwaitBuzzer  => self.forState.players.firstPlayer
  AwaitScore   => self.forState.players.firstPlayer
  Done         => Just self.forState

||| Get the current player's name, if it has one.
(.player)
  : {state : State}
  -> Game state p
  -> Maybe Player
(.player) game = pure $ index !game.playerID game.players

||| Get the monetary value of the given cell
(.cellValue) : Game state p -> p.CellID -> Nat
(.cellValue) self cell = self.board.cellValue cell

||| Update the given player's score by the given amount
(.adjustScore)
  : {state : State}
  -> Game state p
  -> p.PlayerID
  -> Integer
  -> Game state p
(.adjustScore) self id value = {
  players $= updateAt id (updateScore value)
} self

||| Mark the given cell as having been played.
(.clearCell)
  :  Game state p
  -> p.CellID
  -> Game state p
(.clearCell) self cell = {free $= delete cell} self

||| True if all the cells have been cleared
(.done) : Game state p -> Bool
(.done) self = self.free == empty

||| Start a turn with the given player.
|||
||| This will abruptly end the current turn.
(.beginTurn)
  :  Game state p
  -> p.PlayerID
  -> Game AwaitCell p
(.beginTurn) self player = {forState := player} self

||| Record the player's cell choice.
(.chooseCell)
  :  Game AwaitCell p
  -> p.CellID
  -> Game ReadQuestion p
(.chooseCell) self cell = ({forState := cell} self).clearCell cell

||| Wait for the players to buzz in.
|||
||| This action is only valid in the ReadQuestion state.
(.armBuzzers)
  :  Game ReadQuestion p
  -> Game AwaitBuzzer p
(.armBuzzers) self = {
  forState := Buzz {players = empty, cell = self.forState}
} self

||| Record the player buzzing in at the given time.
|||
||| This action is only valid
(.buzzIn)
  :  Game AwaitBuzzer p
  -> p.PlayerID
  -> Nat
  -> Game AwaitBuzzer p
(.buzzIn) self player time = {
  forState := {players $= insert player time} self.forState
} self

(.lockBuzzers) : Game AwaitBuzzer p -> Game AwaitScore p
-- odd construction here is consequence of this being a dependent
-- record.
--
-- XXX: is there an idiom for an empty record update?
(.lockBuzzers) self = {forState := self.forState} self

||| Clear the current cell, and reset the game state.
|||
||| This is a helper function, and always succeeds.
(.endTurn)
  :  Game _ p
  -> Game AwaitPlayer p
(.endTurn) self = {forState := ()} self

||| Advance to the next player.
(.nextPlayer) : Game AwaitScore p -> Game AwaitScore p
(.nextPlayer) self = {
  forState := {players $= (.next)} self.forState
} self

||| Adjust the current score for the player.
|||
||| If the player got the answer right, then increase their balance
||| by the cell amount and start the next turn.
|||
||| If the player got the answer wrong, decrease the balance by the
||| cell amount, and give the next player (if any) a chance to answer
||| the question.
(.scorePlayer)
  :  Game AwaitScore p
  -> Bool
  -> Either (Game AwaitScore p) (Game AwaitPlayer p)
(.scorePlayer) self correct = let
  Buzz players cell = self.forState
  value : Integer = cast $ self.cellValue cell
  in case players.firstPlayer of
    Nothing => Right $ self.endTurn
    Just p  => case correct of
      True => Right $ self.endTurn.adjustScore p value
      False => Left $ (self.adjustScore p (-(cast value))).nextPlayer

||| These are the actions which affect the game state.
export
data Action : (p : Params) -> Type where
  ChoosePlayer : p.PlayerID -> Action p
  ChooseCell   : p.CellID -> Action p
  Advance      : Action p
  BuzzIn       : p.PlayerID -> Nat -> Action p
  Score        : Bool -> Action p

||| Top-level game, with embedded state.
record App p where
  constructor A
  state : State
  game  : Game state p

||| A helper function for defining the game state machine.
continue
  :  {state : State}
  -> Game state p
  -> Either String (App p)
continue {state} game = Right $ A state game

export
handle
  :  App p
  -> Action p
  -> Either String (App p)
handle (A AwaitPlayer  g) (ChoosePlayer p) = continue $ g.beginTurn p
handle (A AwaitCell    g) (ChooseCell   c) = continue $ g.chooseCell c
handle (A ReadQuestion g) Advance          = continue $ g.armBuzzers
handle (A AwaitBuzzer  g) (BuzzIn p t)     = continue $ g.buzzIn p t
handle (A AwaitBuzzer  g) Advance          = continue $ g.lockBuzzers
handle (A AwaitScore   g) (Score correct)  = case g.scorePlayer correct of
  Left  nextPlayer => continue $ nextPlayer
  Right endOfTurn  => continue $ endOfTurn
handle (A Done         g) _ = Left "\{show $ name <$> g.player} wins"
handle _                  _ = Left "Invalid Action"
