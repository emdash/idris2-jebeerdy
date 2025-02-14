module Main


import Data.List
import Data.Vect
import Data.SortedMap
import Data.SortedSet


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
  values     : Vect cols Nat
  cells      : Vect cols (Vect rows Cell)
  final      : Cell

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

||| A reference to a cell position.
|||
||| The row and column indicies must be valid.
0 CellID : (0 rows : Nat) -> (0 cols : Nat) -> Type
CellID rows cols = (Fin rows, Fin cols)

||| Get the player who buzzed in first
(.firstPlayer) : SortedMap (PlayerID np) Nat -> Maybe (PlayerID np)
(.firstPlayer) buzzed = map fst $ head' $ sortBy buzzerTime $ toList buzzed
  where
    buzzerTime : (PlayerID np, Nat) -> (PlayerID np, Nat) -> Ordering
    buzzerTime (p1, t1) (p2, t2) = compare t1 t2

||| Remove the player who buzzed in first, making the next player the 'first'.
(.nextPlayer) : SortedMap (PlayerID np) Nat -> SortedMap (PlayerID np) Nat
(.nextPlayer) buzzed = case buzzed.firstPlayer of
  Nothing => empty
  Just p => delete p buzzed

||| These are the actions which affect the game state.
data Action : (rows : Nat) -> (cols : Nat) -> (np : Nat) -> Type where
  ChoosePlayer : PlayerID n -> Action rows cols n
  ChooseCell   : CellID rows cols -> Action rows cols np
  Advance      : Action rows cols np
  BuzzIn       : PlayerID n -> Action rows cols n
  Score        : Bool -> Action rows cols np

||| The current state of play, which is used to determine which actions are valid.
data State : Nat -> Nat -> Nat -> Type where
  AwaitPlayer   : State rows cols np
  AwaitCell     : PlayerID np -> State rows cols np
  ReadQuestion  : PlayerID np -> CellID rows cols -> State rows cols np
  AwaitBuzzer   : SortedMap (PlayerID np) Nat -> CellID rows cols -> State rows cols np
  AwaitScore    : SortedMap (PlayerID np) Nat -> CellID rows cols -> State rows cols np
  Done          : State rows cols np

||| The entire game state, information common to all game states.
record Game (rows : Nat) (cols : Nat) (np : Nat) where
  constructor MkGame
  board   : Board 6 5
  players : Vect np String
  free    : SortedSet (CellID rows cols)
  error   : Maybe String
  state   : State rows cols np

||| The current player, if the game can be said to have one.
(.player) : Game rows cols np -> Maybe (PlayerID np)
(.player) game = case game.state of
  AwaitPlayer            => Nothing
  (AwaitCell id)         => Just id
  (ReadQuestion id _)    => Just id
  (AwaitBuzzer buzzed _) => buzzed.firstPlayer
  (AwaitScore  buzzed _) => buzzed.firstPlayer
  Done                   => Nothing

||| Get the current player's name, if it has one.
(.playerName) : Game rows cols np -> Maybe String
(.playerName) game = pure $ index !game.player game.players

||| The transition function for the game's state machine.
transition : Game rows cols np -> Action rows cols np -> Game rows cols np
transition game = go game.state
  where
    ||| Helper function which handles users buzzing in
    buzzIn : PlayerID np -> State rows cols np -> State rows cols np

    ||| Advance to next player, or end the game
    endTurn : CellID rows cols -> Game rows cols np -> Game rows cols np

    ||| Helper function
    scorePlayer
      :  SortedMap (PlayerID np) Nat
      -> Bool
      -> CellID rows cols
      -> Game rows cols np
      -> Game rows cols np
    scorePlayer buzzed correct cell game = case buzzed.firstPlayer of
      Nothing => endTurn cell game
      Just p  => case correct of
        True => endTurn cell game
        False => {state := AwaitScore buzzed.nextPlayer cell} game

    ||| Helper function to set error messages
    error : String -> Game rows cols np -> Game rows cols np
    error msg = {error := Just msg}

    ||| Main table of transitions.
    go : State rows cols np -> Action rows cols np -> Game rows cols np
    go AwaitPlayer (ChoosePlayer player)     = {state := AwaitCell player} game
    go (AwaitCell player) (ChooseCell cell)  = {state := ReadQuestion player cell} game
    go (ReadQuestion _ cell) Advance         = {state := AwaitBuzzer empty cell} game
    go (AwaitBuzzer buzzed cell) (BuzzIn id) = {state $= buzzIn id} game
    go (AwaitBuzzer buzzed cell) Advance     = {state := AwaitScore buzzed cell} game
    go (AwaitScore  buzzed cell) (Score c)   = scorePlayer buzzed c cell game
    go Done _                                = game
    go _           _                         = error "Invalid Action" game





main : IO ()
main = putStrLn "Hello from Idris2!"
