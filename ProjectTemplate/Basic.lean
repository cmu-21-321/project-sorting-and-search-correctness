import Mathlib

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
