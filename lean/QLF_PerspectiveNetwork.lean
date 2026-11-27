import QLF_SharedReality
import QLF_ColourClosure
import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option linter.unusedVariables false

/-!
# QLF_PerspectiveNetwork — shared closures among perspectives need not be tree-shaped

Part of the [Quantum Logical Framework (QLF)](../README.md). **ZFA** (Zero Free Action) is equal and
opposite quantum logical action with zero free energy, the principle of QLF. Companion:
[`Colour_Closure.md`](../Colour_Closure.md) §7; candidate principle C23 in
[`Principles.md`](../Principles.md).

Perspectives are the three bodies of [`QLF_SharedReality`](QLF_SharedReality.lean): a token is a
twist tagged with the body (`Tok3 = Fin 3 × Twist`) that contributes it, assigned before any closure is
evaluated. A word **closes jointly** when the twists of all bodies together are count-balanced.

* **RP0 `shared_closure_cycle_exists`.** Three events `A> B<`, `B> C<`, `C> A<`: each closes jointly,
  no body's part of any event closes, and every body closes over the three events.
* **RP1 `tree_edges_insufficient`.** Any graph on the three perspectives that has the three direct
  shared-closure relations as edges has a cycle, so it is not a tree. This step is graph theory
  (bookkeeping): the content is RP0's witness. It does not exclude a tree that uses mediator nodes or
  represents a relation by a path.
* **RP2 `irreducible_three_way_closure`.** The proton closure `>^/<\v` split as `A = >v`,
  `B = ^\`, `C = /<` (each body's twists in word order): the word closes jointly and carries baryon
  number 1, yet no body closes and **no pair of bodies closes**. The closure is irreducibly
  three-way. The three nets are `x−y`, `y−z`, `z−x`.
* **RP4 (partial) `gauge_keeps_winding_moves_colour`.** Inserting a gauge twist keeps the junction
  winding (`junction_insert_gauge`) and changes the total `F₃²` colour by the nonzero label of `+`.
  So winding is gauge-blind and this colour reading is not. Which invariant the gauge axis carries
  between perspectives (RP5) is open.

No axioms. Not here: RP3 (laminarity), RP5–RP7 (the fourth axis as a relation between perspectives,
and recovery of three axes at an emergent level), which are conjectures.
-/

namespace QLF.PerspectiveNetwork

open QLF QLF.SharedReality QLF.BaryonWinding QLF.ColourFlux QLF.ColourClosure

/-- A word of tagged twists **closes jointly**: all bodies' twists together are count-balanced. -/
def JointClosed (w : List Tok3) : Prop := countBalanced (w.map Prod.snd)

instance (w : List Tok3) : Decidable (JointClosed w) := by
  unfold JointClosed countBalanced; infer_instance

instance (i : Fin 3) (w : List Tok3) : Decidable (BodyZFA i w) := by
  unfold BodyZFA countBalanced; infer_instance

/-- The part of a word contributed by a set of bodies. -/
def partOf (S : Fin 3 → Bool) (w : List Tok3) : List Tok3 := w.filter (fun p => S p.1)

-- ============================================================================
-- RP0  A cycle of pairwise shared closures
-- ============================================================================

def eAB : List Tok3 := [(0, Twist.right), (1, Twist.left)]
def eBC : List Tok3 := [(1, Twist.right), (2, Twist.left)]
def eCA : List Tok3 := [(2, Twist.right), (0, Twist.left)]

/-- **RP0.** Each of the three events closes jointly; in each, neither contributing body closes by
    itself; over all three events every body closes. -/
theorem shared_closure_cycle_exists :
    (JointClosed eAB ∧ JointClosed eBC ∧ JointClosed eCA) ∧
    (¬ BodyZFA 0 eAB ∧ ¬ BodyZFA 1 eAB) ∧
    (¬ BodyZFA 1 eBC ∧ ¬ BodyZFA 2 eBC) ∧
    (¬ BodyZFA 2 eCA ∧ ¬ BodyZFA 0 eCA) ∧
    GlobalZFA (eAB ++ eBC ++ eCA) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, ?_⟩
  intro i
  fin_cases i <;> decide

-- ============================================================================
-- RP1  A tree cannot carry the three relations as edges
-- ============================================================================

/-- **RP1.** A graph on three perspectives with all three direct relations as edges contains the
    cycle `0 → 1 → 2 → 0`, so it is not acyclic and not a tree. -/
theorem tree_edges_insufficient (G : SimpleGraph (Fin 3))
    (h01 : G.Adj 0 1) (h12 : G.Adj 1 2) (h20 : G.Adj 2 0) : ¬ G.IsAcyclic := by
  intro hac
  apply hac (SimpleGraph.Walk.cons h01 (SimpleGraph.Walk.cons h12
    (SimpleGraph.Walk.cons h20 SimpleGraph.Walk.nil)))
  rw [SimpleGraph.Walk.cons_isCycle_iff]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.Walk.isPath_def]
    simp [SimpleGraph.Walk.support]
  · simp [SimpleGraph.Walk.edges]

theorem tree_edges_insufficient' (G : SimpleGraph (Fin 3))
    (h01 : G.Adj 0 1) (h12 : G.Adj 1 2) (h20 : G.Adj 2 0) : ¬ G.IsTree :=
  fun ht => tree_edges_insufficient G h01 h12 h20 ht.isAcyclic

-- ============================================================================
-- RP2  An irreducible three-way closure
-- ============================================================================

/-- The proton closure with provenance: `A = >v`, `B = ^\`, `C = /<`. -/
def protonTagged : List Tok3 :=
  [(0, Twist.right), (1, Twist.up), (2, Twist.slash), (2, Twist.left), (1, Twist.backslash),
    (0, Twist.down)]

/-- **RP2.** The tagged proton word is the proton closure, closes jointly and has baryon number 1;
    no single body closes and no pair of bodies closes. -/
theorem irreducible_three_way_closure :
    protonTagged.map Prod.snd = Manifestation.protonClosure ∧
    JointClosed protonTagged ∧
    junctionBaryon (protonTagged.map Prod.snd) = 1 ∧
    (∀ i : Fin 3, ¬ BodyZFA i protonTagged) ∧
    ¬ JointClosed (partOf (fun i => i ≠ 2) protonTagged) ∧
    ¬ JointClosed (partOf (fun i => i ≠ 0) protonTagged) ∧
    ¬ JointClosed (partOf (fun i => i ≠ 1) protonTagged) := by
  refine ⟨by decide, by decide, by decide, ?_, by decide, by decide, by decide⟩
  intro i
  fin_cases i <;> decide

-- ============================================================================
-- RP4 (partial)  What a gauge twist keeps and what it moves
-- ============================================================================

/-- **Gauge keeps the winding and moves the colour.** Inserting `+` anywhere leaves the junction
    baryon number unchanged and adds the nonzero colour label of `+` to the total colour. -/
theorem gauge_keeps_winding_moves_colour (l r : List Twist) :
    junctionBaryon (l ++ Twist.plus :: r) = junctionBaryon (l ++ r) ∧
    colourTotal (l ++ Twist.plus :: r) = colourTotal (l ++ r) + colVec Twist.plus ∧
    colVec Twist.plus ≠ 0 := by
  refine ⟨junction_insert_gauge l r Twist.plus rfl, ?_, colVec_ne_zero _⟩
  rw [colourTotal_append, colourTotal_cons, colourTotal_append]
  abel

end QLF.PerspectiveNetwork
