import Mathlib
import Mathlib.Order.Lattice

/-!
# Insertion sort
# first arg to insertion sort "map" dictates what list is sorted on
-/
-- Guarantees total ordering, every two elements are comparable
variable {α c : Type} [LinearOrder c]

-- namespace Proj


def orderedInsert (map : α -> c) (a : α) : List α -> List α
  | [] => [a]
  | b::rest => if (map a) ≤ (map b) then a::b::rest
               else b::orderedInsert map a rest

def insertionSort (map : α -> c) : List α -> List α
  | [] => []
  | a::rest => orderedInsert map a (insertionSort map rest)

-- end Proj


-- test case

structure Student where
  name : String
  grade : ℕ
  stID : ℕ

def students : List Student :=
[⟨"Teresa", 3, 3030⟩, ⟨"Sid", 3, 1010⟩, ⟨"Ria", 3, 2020⟩]

-- sort by ID
#eval List.map Student.name (insertionSort Student.stID students)

-- sort by name
#eval List.map Student.name (insertionSort Student.name students)

-- sort by grade: every grade ties, output = input (order of elements should not change)
#eval List.map Student.name (insertionSort Student.grade students)



-- correctness proofs
def checkSorted (f : α → c) : List α → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest =>
    if f a ≤ f b then checkSorted f (b :: rest)
    else false

#eval checkSorted Student.stID (insertionSort Student.stID students)
-- should be true
#eval checkSorted Student.stID students
-- students has yet to be sorted, so should  be false
#eval checkSorted Student.stID ([] : List Student)
-- should be true

-- precondition and postcondition

-- precondition set up
-- redundant with checkSorted, will determine which one to develop further next week
inductive SortedBy (f : α → c) : List α → Prop
  | nil : SortedBy f []
  | single (x : α) : SortedBy f [x]
  | cons (x y : α) (l : List α) :
    f x ≤ f y → SortedBy f (y :: l) → SortedBy f (x :: y :: l)

theorem orderedInsert_sorted (f : α → c) (a : α) (l : List α)
    (h : SortedBy f l) :
    SortedBy f (orderedInsert f a l) := by
    sorry


-- proving trivial facts using sorting defns set up so far
theorem exercise01 (f : α → c) (a : α) :
    orderedInsert f a [] = [a] := by
  rfl

theorem exercise02 (f : α → c) (a b : α) (rest : List α) (h : f a ≤ f b) :
    orderedInsert f a (b :: rest) = a :: b :: rest := by
  rw [orderedInsert]
  simp [h]

theorem exercise03 (f : α → c) (a b : α) (rest : List α) (h : ¬ f a ≤ f b) :
    orderedInsert f a (b :: rest) = b :: orderedInsert f a rest := by
  rw [orderedInsert]
  simp [h]

theorem exercise04 (f : α → c) :
    insertionSort f [] = [] := by
  rfl

theorem exercise05 (f : α → c) (a : α) (rest : List α) :
    insertionSort f (a :: rest) = orderedInsert f a (insertionSort f rest) := by
  rfl

theorem orderedInsert_perm (f : α → c) (a : α) (l : List α) :
    (orderedInsert f a l).Perm (a :: l) := by
  induction l with
  | nil =>
    rw [exercise01]
  | cons b rest ih =>
    by_cases h : f a ≤ f b
    · rw [exercise02 f a b rest h]
    · rw [exercise03 f a b rest h]
      exact (List.Perm.cons b ih).trans (List.Perm.swap a b rest)

theorem insertionSort_perm (f : α → c) (l : List α) :
    (insertionSort f l).Perm l := by
  induction l with
  | nil =>
    rw [exercise04]
  | cons a rest ih =>
    rw [exercise05]
    exact (orderedInsert_perm f a (insertionSort f rest)).trans (List.Perm.cons a ih)

#min_imports
