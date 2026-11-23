/-
# QLF_AssemblyIndex

Stage 1 of the Lean layer for issue #264 ([`Assembly_Index_QLF.md`](../Assembly_Index_QLF.md)):
the **flat-sector assembly index** with unlimited reuse.

An *assembly pathway* is a list of twist words built one entry at a time.  Each entry is either a
primitive (a single twist, free) or the join `a ++ b` of two words already on the pathway (one
join).  Earlier entries can be reused any number of times.  `Pathway p n` says `p` is a pathway
using `n` joins.  The assembly index `assemblyIndex w` is the least `n` such that some pathway
with `n` joins contains `w`.  This is the minimum-SLP-size index of `assembly_index.py` (the
ordinary `a(x)`).

Proved here:

* `assembles_length_sub_one`: every nonempty word is assembled with `|w| − 1` joins (the left
  comb), so `assemblyIndex_le_length_sub_one`.
* `reuse_saves_a_join`: `^v^v` is assembled with 2 joins, fewer than `|w| − 1 = 3`, so reuse does
  work and the bound is not an equality.

The closure-constrained index `a_ZFA` (stage 2: only closed intermediates reusable, open ones
consumed once) and `assemblyIndex_le_closed` remain open.

No axioms.  Part of [Quantum Logical Framework (QLF)](../README.md).
-/

import QLF_TwistAlphabet

namespace QLF.AssemblyIndex

open QLF

/-- A twist word. -/
abbrev Word := List Twist

/-- `Pathway p n`: `p` is an assembly pathway that uses `n` joins.  Primitives are free; a join
appends the concatenation of two words already on the pathway. -/
inductive Pathway : List Word → Nat → Prop
  | nil : Pathway [] 0
  | prim {p : List Word} {n : Nat} (t : Twist) : Pathway p n → Pathway (p ++ [[t]]) n
  | join {p : List Word} {n : Nat} {a b : Word} :
      Pathway p n → a ∈ p → b ∈ p → Pathway (p ++ [a ++ b]) (n + 1)

/-- `w` can be assembled with `n` joins. -/
def Assembles (w : Word) (n : Nat) : Prop := ∃ p, Pathway p n ∧ w ∈ p

/-- **Linear bound.**  Every nonempty word is assembled with `|w| − 1` joins. -/
theorem assembles_length_sub_one (w : Word) (hw : w ≠ []) : Assembles w (w.length - 1) := by
  induction w using List.reverseRecOn with
  | nil => exact absurd rfl hw
  | append_singleton u t ih =>
    by_cases hu : u = []
    · subst hu
      exact ⟨[[t]], by simpa using Pathway.prim t Pathway.nil, by simp⟩
    · obtain ⟨p, hp, hmem⟩ := ih hu
      have hlen : u.length ≠ 0 := by simpa [List.length_eq_zero_iff] using hu
      refine ⟨(p ++ [[t]]) ++ [u ++ [t]], ?_, by simp⟩
      have h := Pathway.join (a := u) (b := [t]) (Pathway.prim t hp)
        (List.mem_append_left _ hmem) (by simp)
      have e : u.length - 1 + 1 = (u ++ [t]).length - 1 := by simp; omega
      rw [e] at h
      exact h

/-- The set of join counts that suffice. -/
def assemblyCosts (w : Word) : Set Nat := {n | Assembles w n}

/-- The **assembly index**: the least number of joins that assembles `w` (with reuse). -/
noncomputable def assemblyIndex (w : Word) : Nat := sInf (assemblyCosts w)

/-- **`a(w) ≤ |w| − 1`** for every nonempty word. -/
theorem assemblyIndex_le_length_sub_one (w : Word) (hw : w ≠ []) :
    assemblyIndex w ≤ w.length - 1 :=
  Nat.sInf_le (assembles_length_sub_one w hw)

/-- **Reuse saves a join.**  `^v^v` is assembled with 2 joins: build `^v`, then join it to
itself.  The comb needs `|w| − 1 = 3`. -/
theorem reuse_saves_a_join :
    Assembles [Twist.up, Twist.down, Twist.up, Twist.down] 2 ∧
    assemblyIndex [Twist.up, Twist.down, Twist.up, Twist.down] <
      [Twist.up, Twist.down, Twist.up, Twist.down].length - 1 := by
  have h : Assembles [Twist.up, Twist.down, Twist.up, Twist.down] 2 := by
    have p0 := Pathway.prim Twist.down (Pathway.prim Twist.up Pathway.nil)
    have p1 := Pathway.join (a := [Twist.up]) (b := [Twist.down]) p0 (by simp) (by simp)
    have p2 := Pathway.join (a := [Twist.up, Twist.down]) (b := [Twist.up, Twist.down]) p1
      (by simp) (by simp)
    exact ⟨_, p2, by simp⟩
  refine ⟨h, ?_⟩
  have := Nat.sInf_le (s := assemblyCosts [Twist.up, Twist.down, Twist.up, Twist.down]) h
  simp only [assemblyIndex, List.length_cons, List.length_nil] at this ⊢
  omega

end QLF.AssemblyIndex
