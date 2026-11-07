import Mathlib
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Order.SuccPred.Nat

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

def ElemSorted (l : List elem) : Prop :=
  List.Pairwise (fun a b => a.key ≤ b.key) l

theorem merge_empty_left (r : List elem) : merge [] r = r := by
  rw [merge]

theorem merge_cons_empty (a : elem) (l : List elem) : merge (a::l) [] = a::l := by
  rw [merge]

theorem merge_cons_cons (a b : elem) (l r : List elem) :
    merge (a::l) (b::r) =
      if a.key ≤ b.key then a :: merge l (b::r) else b :: merge (a::l) r := by
  rw [merge]

-- merge_perm: merge l r has exactly the same elts as l ++ r
-- just possibly in a different order

theorem merge_perm : ∀ (l r : List elem), (merge l r).Perm (l ++ r)
  | [], r => by
    rw [merge_empty_left, List.nil_append]
  | a::l, [] => by
    rw [merge_cons_empty, List.append_nil]
  | a::l, b::r => by
    by_cases h : a.key ≤ b.key
    · rw [merge_cons_cons]
      simp only [h, ↓reduceIte, List.cons_append]
      exact List.Perm.cons a (merge_perm l (b::r))
    · rw [merge_cons_cons]
      simp only [h, ↓reduceIte]
      exact (List.Perm.cons b (merge_perm (a::l) r)).trans List.perm_middle.symm

#eval split [⟨1, "a"⟩, ⟨2, "b"⟩]
#eval split [⟨1, "a"⟩, ⟨2, "b"⟩, ⟨3, "c"⟩, ⟨4, "d"⟩, ⟨5, "e"⟩]

#eval merge [] [⟨1, "a"⟩]
#eval merge [⟨1, "a"⟩] []
#eval merge [⟨1, "a"⟩, ⟨4, "b"⟩] [⟨2, "c"⟩, ⟨3, "d"⟩]


inductive Sorted : List Nat → Prop
  | nil : Sorted []
  | single (x : Nat) : Sorted [x]
  | cons (x y : Nat) (rest : List Nat) :
      x ≤ y → Sorted (y :: rest) → Sorted (x :: y :: rest)

def nth : List Nat → Nat → Option Nat
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, i + 1 => nth xs i

def Contains (l : List Nat) (x : Nat) : Prop := ∃ i, nth l i = some x


def bsearchGo (l : List Nat) (target : Nat) (lo hi : Nat) : Option Nat :=
  if _h : lo < hi then
    let mid := lo + (hi - lo) / 2
    match nth l mid with
    | none => none
    | some v =>
      if target < v then
        bsearchGo l target lo mid
      else if v < target then
        bsearchGo l target (mid + 1) hi
      else
        some mid
  else
    none
termination_by hi - lo
decreasing_by all_goals omega

def binarySearch (l : List Nat) (target : Nat) : Option Nat :=
  bsearchGo l target 0 l.length


#eval binarySearch [] 5
#eval binarySearch [5] 5
#eval binarySearch [5] 7
#eval binarySearch [1, 3, 5, 7, 9] 1
#eval binarySearch [1, 3, 5, 7, 9] 5
#eval binarySearch [1, 2, 4, 8, 16, 32] 16


theorem bsearchGo_sound (l : List Nat) (target lo hi i : Nat) :
    bsearchGo l target lo hi = some i → nth l i = some target := by
  sorry

theorem binarySearch_sound (l : List Nat) (x i : Nat) :
    binarySearch l x = some i → nth l i = some x := by
  sorry

theorem binarySearch_complete (l : List Nat) (x : Nat) :
    Sorted l → Contains l x → ∃ i, binarySearch l x = some i := by
  sorry

#min_imports
