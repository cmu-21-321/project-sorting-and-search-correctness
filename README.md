# Sorting and Search Correctness

We define insertion sort and merge sort, prove both return a sorted permutation of the input,
prove stability, and prove binary search correct on sorted lists.

## Binary search

Code: `ProjectTemplate/Basic.lean`.

### Definitions

All of these are written from scratch rather than taken from a library.

- `Sorted : List Nat → Prop` says a list is in non-decreasing order. It is an inductive
  predicate with three rules: the empty list is sorted, a one-element list is sorted, and
  `x :: y :: rest` is sorted when `x ≤ y` and `y :: rest` is sorted.
- `nth l i : Option Nat` returns the element at index `i`, or `none` if `i` is out of range.
- `Contains l x` means `x` appears in `l`, stated as `∃ i, nth l i = some x`.
- `bsearchGo l target lo hi` searches the indices from `lo` up to (but not including) `hi`.
  It looks at the middle element and either returns its index or recurses on the left or
  right half. It terminates because `hi - lo` gets smaller on every call.
- `binarySearch l x` runs `bsearchGo` on the whole list (from `0` to `l.length`).

### What we proved

| Theorem | Meaning |
|---|---|
| `binarySearch_sound` | If binary search returns `some i`, then index `i` really holds `x`. This holds for any list, sorted or not. |
| `binarySearch_complete` | On a sorted list, if `x` is in the list, binary search finds it. |
| `binarySearch_eq_none_iff` | On a sorted list, binary search returns `none` exactly when `x` is not in the list. |

### How the proofs work

- **Soundness:** the function only returns `some mid` right after checking that the middle
  element equals the target, so whatever it returns is correct. The proof is induction that
  follows the branches of `bsearchGo` (`fun_induction`).
- **Completeness:** the key fact is `Sorted.nth_le_nth`: in a sorted list, an earlier index
  holds a value less than or equal to a later index. The main lemma, `bsearchGo_complete`, keeps
  the invariant "if `x` is in the list, it is somewhere between `lo` and `hi`." When the target
  is smaller than the middle element, `Sorted.nth_le_nth` shows it cannot be in the right half,
  so searching only the left half loses nothing (and the same for the other side).
- **Absent case:** if `x` is not in the list, binary search cannot return `some i`, because
  soundness would then show `x` is at index `i`. Together with completeness this gives
  `binarySearch_eq_none_iff`.
- Two small helper lemmas, `nth_lt_length` and `nth_of_lt_length`, connect `nth` to
  `l.length`. They are used to show the search always looks at a real index.

### Tests

`#eval` tests in the same file cover the empty list, a one-element list (found and not found),
the target at the first, middle and last position, and an even-length list.

## Prerequisites

Install Lean via [elan](https://github.com/leanprover/elan) (see the
[Lean installation guide](https://lean-lang.org/install/)). The correct Lean version is
picked up automatically from `lean-toolchain`.

## 1. Rename the project

After creating your repository from this template, rename it from `ProjectTemplate` to your
own project name:

```bash
./customize.sh MyProject
```

This updates `lakefile.toml`, `lake-manifest.json`, the Lean imports and this README's title, and
renames `ProjectTemplate.lean` and `ProjectTemplate/` to `MyProject.lean` and `MyProject/`.
The name must be a valid Lean module name (letters, digits and underscores, starting with a
letter; UpperCamelCase is conventional). Commit the result, then delete `customize.sh`.

## 2. Get the Mathlib cache

Compiling Mathlib from source takes hours, so download the prebuilt files instead:

```bash
lake exe cache get
```

Re-run this whenever you change the Mathlib version (or if your editor starts rebuilding
Mathlib files).

## 3. Build and work on the project

```bash
lake build
```

- Put your Lean files under `MyProject/` and import each one from `MyProject.lean`, so that
  `lake build` (and CI) checks them.
- Open the repository folder (not a single file) in VS Code with the Lean 4 extension.

## Updating Mathlib

Change the `rev` under `[[require]]` in `lakefile.toml` to the new Mathlib tag, and set
`lean-toolchain` to match. Then run:

```bash
lake update mathlib
lake exe cache get
lake build
```

Alternatively, run the **Update Dependencies** workflow from the GitHub *Actions* tab: it
opens a pull request if the update builds, or an issue if it doesn't. (Uncomment the
`schedule` block in `.github/workflows/update.yml` to run it automatically.)

## GitHub setup

- **CI**: every push and pull request is built by `.github/workflows/lean_action_ci.yml`.
- To let the update workflow open pull requests, go to **Settings → Actions → General** and
  tick **Allow GitHub Actions to create and approve pull requests**.
- To publish docs to GitHub Pages, set **Settings → Pages → Source** to "GitHub Actions" and
  uncomment the `docgen-action` line in `lean_action_ci.yml`.
