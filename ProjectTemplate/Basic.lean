import Mathlib

/-!
# Insertion sort
# first arg to insertion sort "map" dictates what list is sorted on
-/
-- Guarantees total ordering, every two elements are comparable
variable {α c : Type} [LinearOrder c]

namespace Proj

def orderedInsert (map : α -> c) (a : α) : List α -> List α
  | [] => [a]
  | b::rest => if (map a) ≤ (map b) then a::b::rest
               else b::orderedInsert map a rest

def insertionSort (map : α -> c) : List α -> List α
  | [] => []
  | a::rest => orderedInsert map a (insertionSort map rest)

end Proj

-- test case

structure Student where
  name : String
  grade : ℕ
  stID : ℕ

def students : List Student :=
[⟨"Teresa", 3, 3030⟩, ⟨"Sid", 3, 1010⟩, ⟨"Ria", 3, 2020⟩]

-- sort by ID
#eval List.map Student.name (Proj.insertionSort Student.stID students)

-- sort by name
#eval List.map Student.name (Proj.insertionSort Student.name students)

-- sort by grade: every grade ties, output = input (order of elements should not change)
#eval List.map Student.name (Proj.insertionSort Student.grade students)


-- Merge Sort

structure elem where
  key : ℕ
  label : String
deriving Repr

--split
def split (l : List elem) : List elem × List elem :=
  (List.take (List.length l / 2) l, List.drop (List.length l / 2) l)

def merge : List elem -> List elem -> List elem
  | [], r => r
  | a::l, [] => a::l
  | a::l, b::r => if a.key ≤ b.key then a::merge l (b::r)
                  else b::merge (a::l) r


#eval split [⟨1, "a"⟩, ⟨2, "b"⟩]
#eval split [⟨1, "a"⟩, ⟨2, "b"⟩, ⟨3, "c"⟩, ⟨4, "d"⟩, ⟨5, "e"⟩]

#eval merge [] [⟨1, "a"⟩]
#eval merge [⟨1, "a"⟩] []
#eval merge [⟨1, "a"⟩, ⟨4, "b"⟩] [⟨2, "c"⟩, ⟨3, "d"⟩]
