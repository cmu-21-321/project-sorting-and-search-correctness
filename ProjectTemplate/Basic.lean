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

--split
def split (l : List elem) : List elem × List elem :=
  (List.take (List.length l / 2) l, List.drop (List.length l / 2) l)

def merge : List elem -> List elem -> List elem
  | [], r => r
  | a::l, [] => a::l
  | a::l, b::r => if a.key ≤ b.key then a::merge l (b::r)
                  else b::merge (a::l) r

end Proj

#eval Proj.insertionSort [⟨2, "a"⟩, ⟨1, "b"⟩, ⟨2, "c"⟩, ⟨1, "d"⟩]
#eval Proj.insertionSort ([] : List elem)


#eval Proj.split [⟨1, "a"⟩, ⟨2, "b"⟩]
#eval Proj.split [⟨1, "a"⟩, ⟨2, "b"⟩, ⟨3, "c"⟩, ⟨4, "d"⟩, ⟨5, "e"⟩]

#eval Proj.merge [] [⟨1, "a"⟩]
#eval Proj.merge [⟨1, "a"⟩] []
#eval Proj.merge [⟨1, "a"⟩, ⟨4, "b"⟩] [⟨2, "c"⟩, ⟨3, "d"⟩]
