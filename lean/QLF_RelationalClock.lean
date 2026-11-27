import QLF_ClosureDepthLaw

/-!
# QLF_RelationalClock — **RC0: identical perspective records, different closure clocks**

The first gate of the relational-capacity bridge (issues #296 and #11; see
[`Planck_Dispersion_Prediction.md`](../Planck_Dispersion_Prediction.md) §5). Three perspectives
`A`, `B`, `C` each contribute the same ordered local word `+ −`. Arrange them two ways:

* **adjacent**: `A+ A− B+ B− C+ C−`, closure depth `1`;
* **nested**:   `A+ B+ C+ C− B− A−`, closure depth `3`.

> **`same_records`** — every perspective's own ordered word is the same in both (`+ −`), and so are
> the totals.
>
> **`different_clocks`** — the adjacent arrangement closes at horizon `1`; the nested one does not,
> and closes first at horizon `3` (`maxExcursion` `1` vs `3`, by `closedAtHorizon_iff_maxExcursion_le`).
>
> **`rc0_record_does_not_determine_clock`** — so no map from the per-perspective record to closure depth
> exists: the factorization condition of issue #296 fails for the closure clock.
>
> **`shuffle_reconstructs`** — the record *plus* the interleaving (which perspective acts at each
> step) reconstructs the history exactly, so it determines the clock. Whether anything smaller than
> the interleaving suffices (RC1) is open.

This strengthens `census_cannot_determine_first_passage` of
[`QLF_ClosureDepthTime`](QLF_ClosureDepthTime.lean) (PR #329), where the multiset of events fails to
fix the latency: here even the ordered word each perspective holds fails. `QLF_ClosureDepthTime`
gives the inventory version for every depth `d` (`same_census_different_latency`); the
perspective-record version is proved here for three perspectives only.

The depth here is the pruning depth on the `pos/neg` phase string, the capacity a horizon needs to
close the history. This is a statement about records and the closure clock; it does not by itself
give a laboratory observable. No axioms.
-/

namespace QLF.RelationalClock

open QLF.HorizonClosure QLF.ClosureDepth

/-- A tagged action: which perspective contributed it, and its phase. -/
abbrev Tok := Fin 3 × TopoElement

def p : TopoElement := .phase .pos
def n : TopoElement := .phase .neg

/-- Independent adjacent closures. -/
def adjacent : List Tok := [(0, p), (0, n), (1, p), (1, n), (2, p), (2, n)]

/-- Nested relational closures. -/
def nested : List Tok := [(0, p), (1, p), (2, p), (2, n), (1, n), (0, n)]

/-- The history a tagged list makes, forgetting who acted. -/
def history (h : List Tok) : TopoString := h.map Prod.snd

/-- A perspective's own ordered record. -/
def record (h : List Tok) (i : Fin 3) : TopoString :=
  (h.filter (fun t => t.1 = i)).map Prod.snd

/-- The interleaving: which perspective acts at each step. -/
def shuffle (h : List Tok) : List (Fin 3) := h.map Prod.fst

theorem same_records : ∀ i : Fin 3, record adjacent i = record nested i := by decide

theorem each_record_is_pair : ∀ i : Fin 3, record nested i = [p, n] := by decide

theorem same_inventory :
    (history adjacent).count p = (history nested).count p ∧
    (history adjacent).count n = (history nested).count n := by decide

theorem adjacent_depth : maxExcursion (history adjacent) = 1 := by decide

theorem nested_depth : maxExcursion (history nested) = 3 := by decide

theorem different_clocks :
    closedAtHorizon 1 (history adjacent) ∧ ¬ closedAtHorizon 1 (history nested) ∧
    ¬ closedAtHorizon 2 (history nested) ∧ closedAtHorizon 3 (history nested) := by
  unfold closedAtHorizon; decide

/-- **RC0.** No function of the per-perspective records gives the closure depth. -/
theorem rc0_record_does_not_determine_clock :
    ¬ ∃ τ : (Fin 3 → TopoString) → ℕ, ∀ h ∈ [adjacent, nested],
        τ (record h) = maxExcursion (history h) := by
  rintro ⟨τ, hτ⟩
  have h1 := hτ adjacent (by simp)
  have h2 := hτ nested (by simp)
  have hr : record adjacent = record nested := funext same_records
  rw [hr, h2, nested_depth, adjacent_depth] at h1
  exact absurd h1 (by decide)

/-- Rebuild a tagged history from the records and the interleaving. -/
def rebuild : List (Fin 3) → (Fin 3 → TopoString) → List Tok
  | [], _ => []
  | i :: is, r =>
    match r i with
    | [] => []
    | e :: es => (i, e) :: rebuild is (Function.update r i es)

/-- **The records plus the interleaving reconstruct the history.** -/
theorem shuffle_reconstructs :
    rebuild (shuffle adjacent) (record adjacent) = adjacent ∧
    rebuild (shuffle nested) (record nested) = nested := by decide

end QLF.RelationalClock
