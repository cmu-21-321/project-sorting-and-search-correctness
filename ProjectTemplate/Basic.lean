import Mathlib

/-!
This file defines sorted lists of natural numbers and proves correctness properties
for binary search on them.
-/
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

theorem nth_lt_length (l : List Nat) (i v : Nat) :
    nth l i = some v → i < l.length := by
  fun_induction nth l i
  · simp_all
  · simp_all
  · simp_all

def bsearchGo (l : List Nat) (target : Nat) (lo hi : Nat)
    (hhi : hi < l.length) (h : lo ≤ hi) : Option Nat :=
  let mid := (lo + hi) / 2
  let v := l[mid]
  if decide (v < target) then
    if h' : mid + 1 ≤ hi then
      bsearchGo l target (mid + 1) hi hhi h' -- c1
    else none -- c2
  else if decide (target < v) then
    if h' : mid ≤ lo then none -- c3
    else
    have h'': lo ≤ mid - 1 := by omega
    bsearchGo l target lo (mid - 1) (by omega) h'' -- c4
  else some v --c5
termination_by hi - lo

def binarySearch (l : List Nat) (target : Nat) : Option Nat :=
  if h : 0 < l.length then
    bsearchGo l target 0 (l.length - 1) (by omega) (Nat.zero_le (l.length - 1))
  else none

#eval binarySearch [] 5
#eval binarySearch [5] 7
#eval binarySearch [1, 3, 5, 7, 9] 5
#eval binarySearch [1, 2, 4, 8, 16, 32] 16

theorem nth_eq_getElem (l : List Nat) (i : Nat) (h : i < l.length) :
    nth l i = some l[i] := by
  fun_induction nth l i
  · grind
  · grind
  · grind

theorem bsearchGo_sound (l : List Nat) (target lo hi : Nat) (hhi : hi < l.length)
    (h : lo ≤ hi) (a : Nat) :
    bsearchGo l target lo hi hhi h = some a → a = target ∧ Contains l target := by
  fun_induction bsearchGo l target lo hi hhi h with
  | case1 _ _ _ _ _ _ _ _ ih => exact ih -- recurse (c1)
  | case2 => intro hres      -- mid + 1 > hi (c2) it fails
             cases hres
  | case3 => intro hres
             cases hres      -- lo gte mid
  | case4 _ _ _ _ _ _ _ _ _ _ ih => exact ih -- recurse (c4)
  | case5 lo hi hhi _ mid v hnlt hngt => -- target found (c5)
    intro hres
    have hm : mid = (lo + hi) / 2 := rfl
    have hSolnPrf : mid < l.length := by omega
    have hv : nth l mid = some v := nth_eq_getElem l mid hSolnPrf
    rw [decide_eq_true_eq] at hnlt hngt
    obtain rfl : v = a := Option.some.inj hres
    -- goal becomes target and existence + contains proof
    have hContains : nth l mid = some target := by
      rw [hv]
      exact congrArg some (by omega)
    exact ⟨by omega, mid, hContains⟩

theorem binarySearch_sound (l : List Nat) (x a : Nat) :
    binarySearch l x = some a → a = x ∧ Contains l x := by
  unfold binarySearch
  split
  · exact bsearchGo_sound l x _ _ _ _ a
  · intro hres
    cases hres

theorem Sorted.nth_le_nth {l : List Nat} (hs : Sorted l) {i j a b : Nat} (hij : i ≤ j)
    (ha : nth l i = some a) (hb : nth l j = some b) : a ≤ b := by -- wts ordering does not change
  induction hs generalizing i j a b with -- induct on list type
  | nil => rw [nth] at ha
           cases ha
  | single x =>
    match i, j with
    | 0, 0 =>
      rw [nth, Option.some.injEq] at ha hb
      omega
    | 0, _ + 1 =>
      rw [nth, nth] at hb
      contradiction
    | _ + 1, _ =>
      rw [nth, nth] at ha
      contradiction
  | cons x y rest hxy _ ih =>
    match i, j with
    | 0, 0 => simp_all [nth]
    | 0, j + 1 =>
      rw [nth, Option.some.injEq] at ha                -- ha : x = a
      have hyb : y ≤ b := ih (Nat.zero_le j) rfl hb    -- y is first in the tail, b is later
      rw [← ha]                                        -- goal becomes x ≤ b
      exact Nat.le_trans hxy hyb
    | _ + 1, 0 => omega
    | i + 1, j + 1 => exact ih (Nat.le_of_succ_le_succ hij) ha hb

theorem bsearchGo_complete {l : List Nat} (hs : Sorted l) {target : Nat}
    (lo hi : Nat) (hhi : hi < l.length) (h : lo ≤ hi)
    (hx : ∃ j, lo ≤ j ∧ j ≤ hi ∧ nth l j = some target) :
    ∃ a, bsearchGo l target lo hi hhi h = some a := by
  obtain ⟨j, hlo, hjhi, hj⟩ := hx -- obtain proofs about positioning of target
  fun_induction bsearchGo l target lo hi hhi h with -- cases are same as b4
  | case1 lo hi hhi _ mid v hlt h' ih =>
    have hm : mid = (lo + hi) / 2 := rfl
    have hv : nth l mid = some v := nth_eq_getElem l mid (by omega)
    rw [decide_eq_true_eq] at hlt
    have hmj : mid < j := by
      rcases Classical.em (j ≤ mid) with hjm | hjm
      · have := hs.nth_le_nth hjm hj hv
        omega
      · omega
    exact ih hmj hjhi
  | case2 lo hi hhi h mid v hlt h' =>
    have hm : mid = (lo + hi) / 2 := rfl
    have hv : nth l mid = some v := nth_eq_getElem l mid (by omega)
    rw [decide_eq_true_eq] at hlt
    have hjm : j ≤ mid := by omega
    have hle : target ≤ v := hs.nth_le_nth hjm hj hv
    omega
  | case3 lo hi hhi _ mid v _ hgt hexit =>
    have hm : mid = (lo + hi) / 2 := rfl
    have hv : nth l mid = some v := nth_eq_getElem l mid (by omega)
    rw [decide_eq_true_eq] at hgt
    have hmj : mid ≤ j := by omega
    have hle : v ≤ target := hs.nth_le_nth hmj hv hj
    omega
  | case4 lo hi hhi _ mid v _ hgt hnexit _ ih =>
    have hm : mid = (lo + hi) / 2 := rfl
    have hv : nth l mid = some v := nth_eq_getElem l mid (by omega)
    rw [decide_eq_true_eq] at hgt                      -- target < v
    have hjm : j < mid := by
      rcases Classical.em (mid ≤ j) with hmj | hmj
      · have := hs.nth_le_nth hmj hv hj
        omega
      · omega
    exact ih hlo (show j ≤ mid - 1 by omega)
  | case5 => exact ⟨_, rfl⟩

theorem binarySearch_complete (l : List Nat) (x : Nat) :
    Sorted l → Contains l x → ∃ a, binarySearch l x = some a := by
  intro hs hc
  obtain ⟨j, hj⟩ := hc
  have hjl : j < l.length := nth_lt_length l j x hj     -- so j is a valid position
  have hne : 0 < l.length := by omega                   -- so the list isn't empty
  have hin : 0 ≤ j ∧ j ≤ l.length - 1 ∧ nth l j = some x :=
    ⟨Nat.zero_le j, by omega, hj⟩                       -- x is inside the window
  unfold binarySearch
  rw [dite_eq_left hne]
  exact bsearchGo_complete hs 0 (l.length - 1) _ _ ⟨j, hin⟩

theorem binSearchAux_eq (l : List Nat) (x : Nat) (lo hi h) :
    Array.binSearchAux (fun a b => decide (a < b)) id l.toArray x lo hi h =
      bsearchGo l x lo hi hi.2 h := by
  fun_induction Array.binSearchAux (fun a b => decide (a < b)) id l.toArray x lo hi h with
  | case1 lo hi h m a hlt hm _ ih =>                  -- core goes right
    rw [bsearchGo]
    simp only [m, a, List.getElem_toArray] at hlt hm
    simp only [hlt, hm]                               -- so ours goes right too
    exact ih
  | case2 lo hi h m a hlt hm _ =>                     -- core: right half empty, none
    rw [bsearchGo]
    simp only [m, a, List.getElem_toArray] at hlt hm
    simp only [hlt, hm]                               -- ours returns none too
    rfl
  | case3 lo hi h m a hnlt hgt hm _ =>                -- core: left half empty, none
    rw [bsearchGo]
    simp only [m, a, List.getElem_toArray] at hnlt hgt hm
    have hm' : (lo.1 + hi.1) / 2 ≤ lo.1 := by omega   -- core's exit test, in our form
    simp only [hnlt, hgt, hm']
    rfl
  | case4 lo hi h m a hnlt hgt hm _ ih =>             -- core goes left
    rw [bsearchGo]
    simp only [m, a, List.getElem_toArray] at hnlt hgt hm
    have hm' : ¬(lo.1 + hi.1) / 2 ≤ lo.1 := by omega  -- core doesn't exit, so ours doesn't
    simp only [hnlt, hgt, hm']
    exact ih
  | case5 lo hi h m a hnlt hngt _ =>                  -- core finds the element
    rw [bsearchGo]
    simp only [m, a, List.getElem_toArray] at hnlt hngt
    simp only [hnlt, hngt]                            -- ours finds the same one
    rfl


theorem binSearch_eq (l : List Nat) (x : Nat) :
    l.toArray.binSearch x (· < ·) = binarySearch l x := by
  cases l with
  | nil => rfl
  | cons a l =>
    unfold Array.binSearch binarySearch
    repeat' split
    all_goals simp_all [binSearchAux_eq]
