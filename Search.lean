/-
  Search.lean — Part C: binary search on sorted lists.
  Everything here is hand-written (no Mathlib, no library list predicates).
-/

/-! ## Spec pieces
  TODO: `Sorted` is a temporary local copy. Replace it with `import Spec`
  once A pushes Spec.lean (A should use this same inductive definition). -/

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


/-- Search for `target` in the half-open index range `[lo, hi)` of `l`. -/
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

/-- Index of `target` in `l` (assumed sorted), or `none` if it isn't there. -/
def binarySearch (l : List Nat) (target : Nat) : Option Nat :=
  bsearchGo l target 0 l.length

/-! ## Tests -/

#eval nth [10, 20, 30] 0   -- some 10
#eval nth [10, 20, 30] 2   -- some 30
#eval nth [10, 20, 30] 3   -- none

example : Sorted [] := Sorted.nil
example : Sorted [1, 2, 3] :=
  Sorted.cons 1 2 [3] (by decide) (Sorted.cons 2 3 [] (by decide) (Sorted.single 3))

-- binarySearch
#eval binarySearch [] 5                      -- none
#eval binarySearch [5] 5                     -- some 0
#eval binarySearch [5] 7                     -- none
#eval binarySearch [1, 3, 5, 7, 9] 1         -- some 0
#eval binarySearch [1, 3, 5, 7, 9] 5         -- some 2
#eval binarySearch [1, 3, 5, 7, 9] 9         -- some 4
#eval binarySearch [1, 3, 5, 7, 9] 0         -- none
#eval binarySearch [1, 3, 5, 7, 9] 10        -- none
#eval binarySearch [1, 3, 5, 7, 9] 4         -- none
#eval binarySearch [2, 2, 2, 2] 2            -- some _
#eval binarySearch [1, 2, 4, 8, 16, 32] 16   -- some 4

/-! ## Correctness (proofs come later) -/

/-- Helper invariant: anything `bsearchGo` returns really holds `target`. -/
theorem bsearchGo_sound (l : List Nat) (target lo hi i : Nat) :
    bsearchGo l target lo hi = some i → nth l i = some target := by
  sorry

/-- Soundness: a returned index points at the target (sortedness not needed). -/
theorem binarySearch_sound (l : List Nat) (x i : Nat) :
    binarySearch l x = some i → nth l i = some x := by
  sorry

/-- Completeness: on a sorted list, if `x` is present, binary search finds it. -/
theorem binarySearch_complete (l : List Nat) (x : Nat) :
    Sorted l → Contains l x → ∃ i, binarySearch l x = some i := by
  sorry
