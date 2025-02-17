module Jebeerdy.Board


import Data.Vect
import JSON.Derive


%language ElabReflection
%default total



||| A reference to a cell position
public export
0 CellID : (0 rows : Nat) -> (0 cols : Nat) -> Type
CellID rows cols = (Fin rows, Fin cols)

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

||| Get a cell by row and column
export
(.get) : CellID rows cols -> Board rows cols -> Cell
-- Dependent types here make it impossible to confuse rows and cols here.
(.get) (i, j) self = index i $ index j self.cells


||| Get the monetary value of the given cell
export
(.cellValue) : Board rows cols -> CellID rows cols -> Nat
(.cellValue) self (i, _) = index i self.values

