import Mathlib

/-!
# Insertion sort on labeled elements
# labels to distinguish elements with duplicate values
-/
structure elem where
  key : ℕ
  label : String
deriving Repr

namespace Proj

def orderedInsert (a : elem) : List elem -> List elem
  | [] => [a]
  | b::rest => if a.key ≤ b.key then a::b::rest
               else b::orderedInsert a rest

def insertionSort : List elem -> List elem
  | [] => []
  | a::rest => orderedInsert a (insertionSort rest)

end Proj

#eval Proj.insertionSort [⟨2, "a"⟩, ⟨1, "b"⟩, ⟨2, "c"⟩, ⟨1, "d"⟩]
#eval Proj.insertionSort ([] : List elem)
