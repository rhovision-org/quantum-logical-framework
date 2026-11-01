import QLF_EdgeSign
import QLF_ColourFlux
import Mathlib.Tactic.Ring

/-!
# Global planar holonomy

Signed area is accumulated from horizontal edges as `y * dx`. This convention
counts winding with multiplicity and works for self-intersecting walks. The
theorems quantify over lists of arbitrary length.
-/

namespace QLF.GlobalHolonomy

open QLF QLF.PhaseRule QLF.EdgeSign QLF.ColourFlux

inductive Step where
  | east | west | north | south
  deriving DecidableEq, Repr

def twist : Step → Twist
  | .east => .right
  | .west => .left
  | .north => .up
  | .south => .down

def dx : Step → ℤ
  | .east => 1
  | .west => -1
  | _ => 0

def dy : Step → ℤ
  | .north => 1
  | .south => -1
  | _ => 0

def xyPos (x y : ℤ) : Axis → ℤ
  | .X => x
  | .Y => y
  | _ => 0

/-- The oriented lattice area contribution from the horizontal edges. -/
def areaAux (x y : ℤ) : List Step → ℤ
  | [] => 0
  | t :: ts => y * dx t + areaAux (x + dx t) (y + dy t) ts

def signedArea (ts : List Step) : ℤ := areaAux 0 0 ts

theorem stepPos_xy (x y : ℤ) (t : Step) :
    stepPos (xyPos x y) (twist t) = xyPos (x + dx t) (y + dy t) := by
  funext a
  cases t <;> cases a <;>
    simp [stepPos, xyPos, twist, dx, dy, twistStep, isNegTwist, axisOf]

private theorem zmod_two_neg (z : ZMod 2) : -z = z := by
  have h : ∀ w : ZMod 2, -w = w := by decide
  exact h z

theorem edgeParity_xy (x y : ℤ) (t : Step) :
    edgeParity (posMod (xyPos x y)) (axisOf (twist t)) =
      ((y * dx t : ℤ) : ZMod 2) := by
  cases t <;>
    simp [edgeParity, posMod, xyPos, twist, dx, dy, axisOf,
      Int.cast_mul, zmod_two_neg]

/-- Discrete Stokes for the fold connection, for every planar word. -/
theorem spin_stokes_from (ts : List Step) (x y : ℤ) :
    holAux (xyPos x y) (ts.map twist) = ((areaAux x y ts : ℤ) : ZMod 2) := by
  induction ts generalizing x y with
  | nil => simp [holAux, areaAux]
  | cons t ts ih =>
      change edgeParity (posMod (xyPos x y)) (axisOf (twist t)) +
          holAux (stepPos (xyPos x y) (twist t)) (ts.map twist) =
        ((y * dx t + areaAux (x + dx t) (y + dy t) ts : ℤ) : ZMod 2)
      rw [stepPos_xy, ih, edgeParity_xy]
      push_cast
      rfl

theorem spin_stokes (ts : List Step) :
    holonomy (ts.map twist) = (signedArea ts : ZMod 2) := by
  exact spin_stokes_from ts 0 0

/-- The full edge product, including the sign of negative steps. -/
theorem spin_connection_area (ts : List Step) :
    connectionPhase (ts.map twist) =
      (-1 : ℤ) ^ negCount (ts.map twist) * sgn (signedArea ts : ZMod 2) := by
  unfold connectionPhase
  rw [connAux_eq, ← holonomy, spin_stokes]

/-- For any balanced planar word its Pauli fold has the area phase. -/
theorem spin_fold_area (ts : List Step)
    (h : countBalanced (ts.map twist)) :
    twistMatrixFold (ts.map twist) =
      ((((-1 : ℤ) ^ negCount (ts.map twist) *
        sgn (signedArea ts : ZMod 2) : ℤ) : ℂ)) • (1 : M) := by
  rw [fold_eq_connectionPhase h, spin_connection_area]

-- A second, independent check: the colour line is transported by the
-- finite Heisenberg group. Its centre records the symplectic cocycle.

structure Trace where
  x : ℤ
  y : ℤ
  area : ℤ
  deriving Repr

def advance (s : Trace) (t : Step) : Trace :=
  ⟨s.x + dx t, s.y + dy t, s.area + s.y * dx t⟩

def trace (ts : List Step) : Trace := ts.foldl advance ⟨0, 0, 0⟩

def colourAdvance (h : Heis) (t : Step) : Heis :=
  h.mul (disp (colVec (twist t)))

def colourWord (ts : List Step) : Heis :=
  ts.foldl colourAdvance ⟨(0, 0), 0⟩

/-- A Heisenberg state encoding displacement and oriented area. -/
def model (s : Trace) : Heis :=
  ⟨((s.y : F3) * (colVec Twist.up).1 + (s.x : F3) * (colVec Twist.right).1,
    (s.y : F3) * (colVec Twist.up).2 + (s.x : F3) * (colVec Twist.right).2),
    (s.x : F3) * (s.y : F3) + (s.area : F3)⟩

theorem colour_step (s : Trace) (t : Step) :
    colourAdvance (model s) t = model (advance s t) := by
  cases t <;>
    simp [colourAdvance, model, advance, Heis.mul, disp, symp,
      colVec, qMat, MatF3.act, twist, dx, dy, Int.cast_add,
      Int.cast_mul, Int.cast_sub, Int.cast_neg] <;>
    ring

/-- Global Heisenberg transport normal form for every planar word. -/
theorem colour_normal_form_from (ts : List Step) (s : Trace) :
    ts.foldl colourAdvance (model s) = model (ts.foldl advance s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      simp only [List.foldl_cons]
      rw [colour_step, ih]

theorem colour_normal_form (ts : List Step) :
    colourWord ts = model (trace ts) := by
  unfold colourWord trace
  have h := colour_normal_form_from ts ⟨0, 0, 0⟩
  simpa [model, colVec, qMat, MatF3.act] using h

/-- The transport trace and the edge integral use the same signed area. -/
theorem trace_area_from (ts : List Step) (s : Trace) :
    (ts.foldl advance s).area = s.area + areaAux s.x s.y ts := by
  induction ts generalizing s with
  | nil => simp [areaAux]
  | cons t ts ih =>
      simp only [List.foldl_cons, areaAux]
      rw [ih]
      simp [advance]
      ring

theorem area_trace (ts : List Step) :
    (trace ts).area = signedArea ts := by
  unfold trace signedArea
  simpa using trace_area_from ts ⟨0, 0, 0⟩

/-- Discrete Stokes for colour on any closed planar walk, at any length. -/
theorem colour_stokes (ts : List Step)
    (hx : (trace ts).x = 0) (hy : (trace ts).y = 0) :
    colourWord ts = ⟨(0, 0), (signedArea ts : F3)⟩ := by
  rw [colour_normal_form]
  simp [model, hx, hy, area_trace]

end QLF.GlobalHolonomy
