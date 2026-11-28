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
> step) reconstructs the history exactly, so it determines the clock. For commuting perspectives
> the records suffice: see the RC1 section below (`relCapacity`).

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

/-! ## Commuting independent perspectives

If actions of different perspectives commute (neither depends on the other), a history is only defined
up to swapping neighbouring actions with different tags. Such swaps never change any perspective's
record (`record_swap`), and they carry the nested arrangement to the adjacent one
(`nested_commutes_to_adjacent`). So within one commutation class the least closure depth is `1`, and
the depth-`3` reading belongs to the nested *order*, which is physical only if the cross-perspective
order is a real dependence. RC0's gap therefore lives exactly in the dependence relation between
perspectives, not in the records. -/

/-- Swapping two neighbouring actions of different perspectives leaves every record unchanged. -/
theorem record_swap (pre post : List Tok) (a b : Tok) (h : a.1 ≠ b.1) (i : Fin 3) :
    record (pre ++ a :: b :: post) i = record (pre ++ b :: a :: post) i := by
  unfold record
  by_cases ha : a.1 = i <;> by_cases hb : b.1 = i
  · exact absurd (ha.trans hb.symm) h
  all_goals simp [List.filter_append, List.filter_cons, ha, hb]

/-- Swap positions `k` and `k+1` when they belong to different perspectives. -/
def swapAt : ℕ → List Tok → Option (List Tok)
  | 0, a :: b :: rest => if a.1 ≠ b.1 then some (b :: a :: rest) else none
  | k + 1, a :: rest => (swapAt k rest).map (a :: ·)
  | _, _ => none

/-- Apply a list of commuting swaps in order. -/
def runSwaps : List ℕ → List Tok → Option (List Tok)
  | [], l => some l
  | k :: ks, l => (swapAt k l).bind (runSwaps ks)

/-- **The nested arrangement commutes to the adjacent one** by six swaps of independent actions:
`A−` moves left past `B−`, `C−`, `C+`, `B+`, then `B−` past `C−`, `C+`. -/
theorem nested_commutes_to_adjacent :
    runSwaps [4, 3, 2, 1, 4, 3] nested = some adjacent := by decide

/-- In the commutation class the closure depth drops from `3` to `1`. -/
theorem commuting_lowers_depth :
    runSwaps [4, 3, 2, 1, 4, 3] nested = some adjacent ∧
    maxExcursion (history nested) = 3 ∧ maxExcursion (history adjacent) = 1 :=
  ⟨nested_commutes_to_adjacent, nested_depth, adjacent_depth⟩

/-! ## A computable reconciliation

`reconcile` closes each perspective's own word before the next one opens: it lays the records end to
end. It is a function, so it can be run on any tagged history; it keeps every record
(`reconcile_record`), so for independent perspectives it stays in the same commutation class; and on
the nested tree it returns the adjacent one (`reconcile_nested`), dropping the depth from `3` to `1`
by moving both ends at once: every perspective's opening and closing actions are brought together. -/

/-- Lay the per-perspective records end to end, in perspective order. -/
def reconcile (h : List Tok) : List Tok :=
  (List.finRange 3).flatMap (fun j => h.filter (fun t => t.1 = j))

theorem filter_filter_tag (h : List Tok) (i j : Fin 3) :
    (h.filter (fun t => t.1 = j)).filter (fun t => t.1 = i) =
      if j = i then h.filter (fun t => t.1 = i) else [] := by
  by_cases hji : j = i
  · subst hji; simp [List.filter_filter]
  · simp only [hji, if_false, List.filter_filter]
    apply List.filter_eq_nil_iff.mpr
    intro t _; simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
    intro h1 h2; exact hji (h2.symm.trans h1)

/-- **Reconciliation keeps every perspective's record.** -/
theorem reconcile_record (h : List Tok) (i : Fin 3) : record (reconcile h) i = record h i := by
  unfold record reconcile
  congr 1
  rw [List.filter_flatMap]
  simp only [filter_filter_tag]
  have hr : List.finRange 3 = [0, 1, 2] := by decide
  rw [hr]
  fin_cases i <;> simp

/-- **On the nested tree, reconciliation returns the adjacent closures.** -/
theorem reconcile_nested : reconcile nested = adjacent := by decide

/-- Depth before and after: `3` and `1`. -/
theorem reconcile_lowers_depth :
    maxExcursion (history nested) = 3 ∧ maxExcursion (history (reconcile nested)) = 1 := by
  rw [reconcile_nested]; exact ⟨nested_depth, adjacent_depth⟩

/-! ## RC1: the relational capacity of independent perspectives

`reconcile` keeps the records but need not minimise depth. With `A = + + − −` and `B = − − + +`, laying
them end to end has depth `2`, while an interleaving of the same records has depth `1`
(`reconcile_not_always_minimal`). The serialization-free quantity is the least depth over every
interleaving the dependencies allow. For independent perspectives these are all shuffles of the
records, so the capacity is a function of the records alone (`relCapacity`); for the example it is
`1` (`relCapacity_example`). A dependency only removes interleavings, so every admitted one has depth
at least the independent capacity (`dependency_increases_capacity`), and the dependency "A closes
before B starts" raises it strictly, from `1` to `2` (`dependency_strict_increase`). That nature
realises the minimum is a proposed reading, not a theorem. -/

/-- All interleavings of two lists that keep each list's own order: the first element of `xs` goes
after some prefix of `ys`, and the rest shuffle with the remaining suffix. -/
def shuffles {α : Type} : List α → List α → List (List α)
  | [], ys => [ys]
  | x :: xs, ys =>
    (List.range (ys.length + 1)).flatMap
      (fun k => (shuffles xs (ys.drop k)).map (fun r => ys.take k ++ x :: r))

/-- The least of a list of depths, starting from a ceiling `c`. -/
def minOver (c : ℕ) (l : List ℕ) : ℕ := l.foldr min c

theorem minOver_le (c : ℕ) : ∀ (l : List ℕ), ∀ y ∈ l, minOver c l ≤ y
  | [], y, hy => by simp at hy
  | x :: xs, y, hy => by
    unfold minOver at *
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hy with h | h
    · subst h; exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (minOver_le c xs y h)

/-- The tagged words of two perspectives. -/
def tagged (i : Fin 3) (w : TopoString) : List Tok := w.map (fun e => (i, e))

def wordA : TopoString := [p, p, n, n]
def wordB : TopoString := [n, n, p, p]

/-- **Relational capacity** of two independent perspectives: the least closure depth over all
interleavings of their records. -/
def relCapacity (wa wb : TopoString) : ℕ :=
  minOver (wa.length + wb.length)
    ((shuffles (tagged 0 wa) (tagged 1 wb)).map (fun h => maxExcursion (history h)))

def serialAB : List Tok := tagged 0 wordA ++ tagged 1 wordB
def interleavedAB : List Tok := [(0, p), (1, n), (0, p), (1, n), (0, n), (1, p), (0, n), (1, p)]

/-- **Reconciliation does not always minimise depth.** Same records, serial depth `2`,
interleaved depth `1`. -/
theorem reconcile_not_always_minimal :
    reconcile interleavedAB = serialAB ∧
    (∀ i : Fin 3, record serialAB i = record interleavedAB i) ∧
    maxExcursion (history serialAB) = 2 ∧ maxExcursion (history interleavedAB) = 1 := by
  decide

theorem relCapacity_example : relCapacity wordA wordB = 1 := by decide +kernel

/-- **Dependencies cannot lower the capacity.** Any interleaving a dependency admits is still an
interleaving, so its depth is at least the independent capacity. -/
theorem dependency_increases_capacity (wa wb : TopoString) (h : List Tok)
    (hh : h ∈ shuffles (tagged 0 wa) (tagged 1 wb)) :
    relCapacity wa wb ≤ maxExcursion (history h) :=
  minOver_le _ _ _ (List.mem_map.mpr ⟨h, hh, rfl⟩)

/-- **A dependency can raise it strictly.** If `A` must close before `B` starts, the only admitted
interleaving is the serial one, depth `2`, against the independent capacity `1`. -/
theorem dependency_strict_increase :
    serialAB ∈ shuffles (tagged 0 wordA) (tagged 1 wordB) ∧
    relCapacity wordA wordB < maxExcursion (history serialAB) := by
  have hhead : (shuffles (tagged 0 wordA) (tagged 1 wordB)).head? = some serialAB := by
    decide +kernel
  refine ⟨List.mem_of_mem_head? hhead, ?_⟩
  rw [relCapacity_example]
  have : maxExcursion (history serialAB) = 2 := by decide
  omega

end QLF.RelationalClock
