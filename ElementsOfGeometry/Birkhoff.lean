import Mathlib


open scoped Real

open scoped Nat

set_option maxHeartbeats 8000000

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

noncomputable section

namespace Birkhoff

section BasicDefinitions

/--
  The undefined elements of the geometry system are points and lines. The undefined relations are distance between points and angle between three points.
-/
structure ElementsUnconditional  where

  -- Points and Lines are undefined types
  Points : Type
  Lines : Type

  -- distance between two points and angle between three points are undefined functions
  dist : Points → Points → ℝ

  -- angle between three points A, O, B is the angle AOB with vertex at O. We need A ≠ O and B ≠ O to define the angle properly. By convention, if either A = O or B = O, then the angle AOB is defined to be 0.
  angle : Points → Points → Points → Real.Angle

/--
  Relations between points and lines: any two points determine a line, and a line determines the set of points lying on it.
-/
structure ElementsUnconditional_with_pt_line_relations extends ElementsUnconditional where

  -- "Any two distinct points determine a unique line" This is postulate II of Birkhoff's axioms; but we include it here as part of the basic definitions to facilitate further development. There are many lines passing through two indentical points, we can choose any one of them in this case. Usually, we will consider the 'horizontal' line passing through two identical points.
  mk_line_pt_pt : Points → Points → Lines

  -- A line determines the set of points lying on it
  get_pts_of_line : Lines → Set Points

  -- For any two points A and B, both A and B lie on the line determined by A and B. "points that make the line, lie on the line"
  mem_pts_line : ∀ A B : Points,
              A ∈ get_pts_of_line (mk_line_pt_pt A B) ∧
              B ∈ get_pts_of_line (mk_line_pt_pt A B)

  -- Any two distinct points lying on a line determine that line. "lines are determined by the points that lie on them"
  eq_line_of_pts : ∀ l : Lines,
              ∀ A B : Points,
              A ≠ B →
              A ∈ get_pts_of_line l →
              B ∈ get_pts_of_line l →
              l = mk_line_pt_pt A B

structure Elements extends ElementsUnconditional_with_pt_line_relations where

  -- Distance is non-negative
  dist_nonneg : ∀ A B : Points, 0 ≤ dist A B

  -- Distance is symmetric
  dist_symm : ∀ A B : Points, dist A B = dist B A

variable (e : Elements)

/--
  Coercion of line into the set of points lying on it.
-/
instance : Coe (e.Lines) (Set e.Points) :=
  ⟨fun l => e.get_pts_of_line l⟩

/--
  Checks if a point p lies on the line
-/
instance : Membership e.Points e.Lines :=
  ⟨fun l p => p ∈ e.get_pts_of_line l⟩

section BasicTheoremsOnLinesAndPoints


/--
  Given points A and B, the line determined by A and B contains both A and Bmk_.
-/
@[simp]
theorem Elements.mem_pts_line' : ∀ A B : e.Points,
            A ∈ e.get_pts_of_line (e.mk_line_pt_pt A B) ∧
              B ∈ e.get_pts_of_line (e.mk_line_pt_pt A B) := e.mem_pts_line

/--
  Given a point A, construct a line passing through A. By default, this line is the horizontal line passing through A.
-/
def Elements.mk_line_pt (A : e.Points) : e.Lines := e.mk_line_pt_pt A A


/--
  The line constructed using a single point A contains the point A.
-/
theorem Elements.pt_on_line_pt (A : e.Points) : A ∈ e.mk_line_pt A := by
  have h := e.mem_pts_line A A
  exact h.1


/--
  If two points A and B lie on both lines l and m, and A ≠ B, then the lines l and m are equal.
-/
@[simp]
theorem Elements.eq_lines_of_pt_pt (l m : e.Lines) (A B : e.Points) (hAB : A ≠ B)  (hAl : A ∈ l) (hBl : B ∈ l) (hAm : A ∈ m) (hBm : B ∈ m) : l = m := by
  have hl : l = e.mk_line_pt_pt A B := e.eq_line_of_pts l A B hAB hAl hBl

  have hm : m = e.mk_line_pt_pt A B := e.eq_line_of_pts m A B hAB hAm hBm

  rw [hl, hm]



/--
  If the line constructed by points A and B is equal to the line constructed by points B and C, then the line constructed by points A and C is equal to the line constructed by points A and B, provided A ≠ C.
-/
theorem Elements.eq_line_of_pt_pt_pt_trans (A B C : e.Points) (hAC : A ≠ C) : e.mk_line_pt_pt A B = e.mk_line_pt_pt B C → e.mk_line_pt_pt A C = e.mk_line_pt_pt A B := by

  intro h_line_eq


  have hA : A ∈ e.get_pts_of_line (e.mk_line_pt_pt A B) := (e.mem_pts_line A B).1

  have hC : C ∈ e.get_pts_of_line (e.mk_line_pt_pt A B) := by

    rw [h_line_eq]
    exact (e.mem_pts_line B C).2

  have hl1 : e.mk_line_pt_pt A B = e.mk_line_pt_pt A C := by
    apply e.eq_line_of_pts (e.mk_line_pt_pt A B) A C hAC hA hC

  rw [← hl1]


/--
  The line constructed using points A and B is the same as the line constructed using points B and A, provided A ≠ B.
-/
theorem Elements.line_pt_pt_sym (A B : e.Points) (hAB : A ≠ B) : e.mk_line_pt_pt A B = e.mk_line_pt_pt B A := by

  have hA : A ∈ e.get_pts_of_line (e.mk_line_pt_pt A B) := (e.mem_pts_line A B).1

  have hB : B ∈ e.get_pts_of_line (e.mk_line_pt_pt A B) := (e.mem_pts_line A B).2

  apply e.eq_line_of_pts (e.mk_line_pt_pt A B) B A hAB.symm hB hA





end BasicTheoremsOnLinesAndPoints


section Definitions_parallel_intersecting_lines

/--
  Two lines are parallel if they do not intersect, i.e., there is no point that lies on both lines. (In plannar geometry, lines are either parallel or intersecting; there are no skew lines.)
-/
def Elements.parallel_lines (l1 l2 : e.Lines) : Prop :=
  ∀ A : e.Points, ¬ (A ∈ l1 ∧ A ∈ l2)

/--
  Two lines are intersecting if there exists a point that lies on both lines. Same lines are considered intersecting.
-/
def Elements.intersecting_lines (l1 l2 : e.Lines) : Prop :=
  ∃ A : e.Points, A ∈ l1 ∧ A ∈ l2


theorem Elements.is_parallel_iff_not_intersecting (l m : e.Lines) : e.parallel_lines l m ↔ ¬ e.intersecting_lines l m := by
  constructor
  · intro h_parallel
    by_contra h_intersecting
    cases h_intersecting with
    | intro A hA =>
      exact h_parallel A hA

  · intro h_not_intersecting
    intro A hA
    exact h_not_intersecting ⟨A, hA⟩

end Definitions_parallel_intersecting_lines

end BasicDefinitions



section PostulateOfLineMeasure




class PostulateI (e : Elements) where
  to_real (l : e.Lines) : e.get_pts_of_line l ≃ ℝ
  eq_dist_eq_real : ∀ l : e.Lines, ∀ A B : e.get_pts_of_line l,
              e.dist A B = |to_real l A - to_real l B|

variable {e : Elements} [P1 :PostulateI e]

#check Classical.choose

section BasicResults

theorem Elements.eq_lines_iff_eq_sets (l m : e.Lines) (hset : (e.get_pts_of_line l) = (e.get_pts_of_line m)) : l = m := by

  let f : e.get_pts_of_line l ≃ ℝ := P1.to_real l

  let A : e.Points := f.invFun 0
  have hA : A = f.invFun 0 := rfl

  let B : e.Points := f.invFun 1
  have hB : B = f.invFun 1 := rfl

  have hAneB : A ≠ B := by
    rw[hA]
    rw[hB]
    have h_distinct : f.invFun 0 ≠ f.invFun 1 := by
      simp +zetaDelta at *;
    -- Since the subtype's equality is equivalent to the underlying type's equality when the elements are in the subtype, we can conclude that the points themselves are distinct.
    -- simp at h_distinct
    convert h_distinct using 1;
    exact ⟨ fun h => Subtype.ext h, fun h => by simp at h ⟩

  have hAl : A ∈ e.get_pts_of_line l := by
    exact Subtype.mem (f.invFun 0)

  have hBl : B ∈ e.get_pts_of_line l := by
    exact Subtype.mem (f.invFun 1)

  have hAm : A ∈ e.get_pts_of_line m := by
    rw[← hset]
    exact hAl

  have hBm : B ∈ e.get_pts_of_line m := by
    rw[← hset]
    exact hBl

  apply e.eq_lines_of_pt_pt l m A B hAneB hAl hBl hAm hBm


theorem Elements.dist_zero (A : e.Points) : e.dist A A = 0 := by
  let l := e.mk_line_pt_pt A A
  have hA : A ∈ e.get_pts_of_line l := (e.mem_pts_line A A).1

  let f : e.get_pts_of_line l ≃ ℝ := P1.to_real l

  let A' : e.get_pts_of_line l := ⟨A, hA⟩

  have h_dist : e.dist A A = |f A' - f A'| := P1.eq_dist_eq_real l A' A'

  rw [sub_self, abs_zero] at h_dist
  exact h_dist

theorem Elements.dist_zero_then_eq (A B : e.Points) (h : e.dist A B = 0) : A = B := by
  by_contra hAB
  let l := e.mk_line_pt_pt A B
  have hA : A ∈ e.get_pts_of_line l := (e.mem_pts_line A B).1
  have hB : B ∈ e.get_pts_of_line l := (e.mem_pts_line A B).2

  let f : e.get_pts_of_line l ≃ ℝ := P1.to_real l

  let A' : e.get_pts_of_line l := ⟨A, hA⟩
  let B' : e.get_pts_of_line l := ⟨B, hB⟩

  have h_dist : e.dist A B = |f A' - f B'| := P1.eq_dist_eq_real l A' B'

  rw [h] at h_dist
  have h_abs : |f A' - f B'| = 0 := h_dist.symm

  have h_eq : f A' - f B' = 0 := abs_eq_zero.1 h_abs

  have h_contra : f A' = f B' := by linarith

  have h_inj : A' = B' := by
    -- Since $f$ is injective, we can conclude that $A' = B'$.
    apply f.injective
    exact h_contra

  have h_points_eq : A = B := by
    -- cases A'
    -- cases B'
    -- Since $f$ is injective, we have $A' = B'$, which implies $A = B$.
    apply congr_arg Subtype.val h_inj

  exact hAB h_points_eq


theorem Elements.dist_sum (l : e.Lines) (A B C : e.Points) (hA : A ∈ l) (hB : B ∈ l) (hC : C ∈ l) (hAB : P1.to_real l ⟨A, hA ⟩  < P1.to_real l ⟨ B, hB⟩ ) (hBC : P1.to_real l ⟨B, hB⟩ < P1.to_real l ⟨C, hC⟩) : e.dist A C = e.dist A B  + e.dist B C := by


  have hAC : P1.to_real l ⟨A, hA⟩  < P1.to_real l ⟨ C, hC⟩ := by
    linarith


  let f : e.get_pts_of_line l ≃ ℝ := P1.to_real l


  let A' : e.get_pts_of_line l := ⟨A, hA⟩
  let B' : e.get_pts_of_line l := ⟨B, hB⟩
  let C' : e.get_pts_of_line l := ⟨C, hC⟩

  have h_dist_AB : e.dist A B = |f A' - f B'| := P1.eq_dist_eq_real l A' B'
  have h_dist_BC : e.dist B C = |f B' - f C'| := P1.eq_dist_eq_real l B' C'
  have h_dist_AC : e.dist A C = |f A' - f C'| := P1.eq_dist_eq_real l A' C'
  have h_leq : ∀ x y : ℝ, x < y → |x - y| = y - x := by
    intro x y hxy
    rw [abs_of_neg (sub_neg.mpr hxy)]
    simp only [neg_sub]

  rw [h_leq (f A') (f B') hAB] at h_dist_AB
  rw [h_leq (f B') (f C') hBC] at h_dist_BC
  rw [h_leq (f A') (f C') hAC] at h_dist_AC

  linarith



theorem Elements.dist_sum_rev (l : e.Lines) (A B C : e.Points) (hA : A ∈ l) (hB : B ∈ l) (hC : C ∈ l) (hAB : P1.to_real l ⟨A, hA ⟩  > P1.to_real l ⟨ B, hB⟩ ) (hBC : P1.to_real l ⟨B, hB⟩ > P1.to_real l ⟨C, hC⟩) : e.dist A C = e.dist A B  + e.dist B C := by


  have hAC : P1.to_real l ⟨A, hA⟩  > P1.to_real l ⟨ C, hC⟩ := by
    linarith


  let f : e.get_pts_of_line l ≃ ℝ := P1.to_real l


  let A' : e.get_pts_of_line l := ⟨A, hA⟩
  let B' : e.get_pts_of_line l := ⟨B, hB⟩
  let C' : e.get_pts_of_line l := ⟨C, hC⟩

  have h_dist_AB : e.dist A B = |f A' - f B'| := P1.eq_dist_eq_real l A' B'
  have h_dist_BC : e.dist B C = |f B' - f C'| := P1.eq_dist_eq_real l B' C'
  have h_dist_AC : e.dist A C = |f A' - f C'| := P1.eq_dist_eq_real l A' C'
  have h_leq : ∀ x y : ℝ, x > y → |x - y| = x - y := by
    intro x y hxy
    rw [abs_of_pos (sub_pos.mpr hxy)]

  rw [h_leq (f A') (f B') hAB] at h_dist_AB
  rw [h_leq (f B') (f C') hBC] at h_dist_BC
  rw [h_leq (f A') (f C') hAC] at h_dist_AC

  linarith

end BasicResults

variable [P1' :PostulateI e]

theorem abcd (l : e.Lines) (f : e.get_pts_of_line l ≃ ℝ ) (g : e.get_pts_of_line l ≃ ℝ ) (h_f : f = P1.to_real l) (h_g : g = P1'.to_real l) : g (f.symm 0) ≠ g (f.symm 1) := by

  simp only [h_f, h_g, g.injective, f.injective]
  simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq, zero_ne_one, not_false_eq_true]



theorem abcd'' (l : e.Lines) (f : e.get_pts_of_line l ≃ ℝ ) (g : e.get_pts_of_line l ≃ ℝ ) (h_f : f = P1.to_real l) (h_g : g = P1'.to_real l) : ∀ A : e.get_pts_of_line l, ( ((g A ≥ g (f.invFun 0)) ∧ (f A ≥ 0)) ∨ (g A ≤ g (f.invFun 0) ∧ f A ≤ 0) →  (g A = f A + g (f.invFun 0)) ) ∧  ( ((g A ≤  g (f.invFun 0)) ∧ (f A ≥ 0)) ∨ (g A ≥  g (f.invFun 0) ∧ f A ≤ 0) → (g A = - (f A) + g (f.invFun 0))) := by
  intro ⟨A, hA⟩
  constructor
  case left =>
    rintro (⟨left, right ⟩| ⟨left, right ⟩ )

    case inl  =>
      calc
      g ⟨ A, hA ⟩ = g ⟨ A, hA ⟩ - g (f.invFun 0) + g (f.invFun 0) := by ring

      _ = |g ⟨ A, hA ⟩ - g (f.invFun 0)| + g (f.invFun 0) := by rw[abs_of_nonneg (sub_nonneg.mpr left)]

      _ = e.dist A (f.invFun 0) + g (f.invFun 0) := by
        rw[h_g]
        rw[P1'.eq_dist_eq_real l ⟨ A, hA ⟩ (f.invFun 0)]

      _ = |f ⟨ A, hA ⟩ - f (f.invFun 0)| + g (f.invFun 0) := by
        rw[P1.eq_dist_eq_real l ⟨ A, hA ⟩ (f.invFun 0)]
        rw[h_f]

      _ = |f ⟨ A, hA ⟩ - 0| + g (f.invFun 0) := by
        simp only [Equiv.invFun_as_coe, Equiv.apply_symm_apply, sub_zero]

      _ = f ⟨ A, hA ⟩ + g (f.invFun 0) := by
        rw[abs_of_nonneg]
        simp only [sub_zero, Equiv.invFun_as_coe]
        simp only [sub_zero]
        exact right

    case inr =>
      calc
      g ⟨ A, hA ⟩ = g ⟨ A, hA ⟩ - g (f.invFun 0) + g (f.invFun 0) := by ring

      _ = - |g ⟨ A, hA ⟩ - g (f.invFun 0)| + g (f.invFun 0) := by
        rw[abs_of_nonpos (sub_nonpos.mpr left)]
        simp only [Equiv.invFun_as_coe, sub_add_cancel, neg_sub]

      _ = - e.dist A (f.invFun 0) + g (f.invFun 0) := by
        rw[h_g]
        rw[P1'.eq_dist_eq_real l ⟨ A, hA ⟩ (f.invFun 0)]

      _ = - |f ⟨ A, hA ⟩ - f (f.invFun 0)| + g (f.invFun 0) := by
        rw[P1.eq_dist_eq_real l ⟨ A, hA ⟩ (f.invFun 0)]
        rw[h_f]

      _ = - |f ⟨ A, hA ⟩ - 0| + g (f.invFun 0) := by
        simp only [Equiv.invFun_as_coe, Equiv.apply_symm_apply, sub_zero]

      _ = f ⟨ A, hA ⟩ + g (f.invFun 0) := by
        rw[abs_of_nonpos]
        simp only [sub_zero, Equiv.invFun_as_coe]
        simp only [neg_neg]
        simp only [sub_zero]
        exact right


  case right =>
    rintro (⟨left, right ⟩| ⟨left, right ⟩ )

    case inl =>
      calc
      g ⟨ A, hA ⟩ = g ⟨ A, hA ⟩ - g (f.invFun 0) + g (f.invFun 0) := by ring

      _ = - |g ⟨ A, hA ⟩ - g (f.invFun 0)| + g (f.invFun 0) := by
        rw[abs_of_nonpos (sub_nonpos.mpr left)]
        simp only [Equiv.invFun_as_coe, sub_add_cancel, neg_sub]

      _ = - e.dist A (f.invFun 0) + g (f.invFun 0) := by
        rw[h_g]
        rw[P1'.eq_dist_eq_real l ⟨ A, hA ⟩ (f.invFun 0)]

      _ = - |f ⟨ A, hA ⟩ - f (f.invFun 0)| + g (f.invFun 0) := by
        rw[P1.eq_dist_eq_real l ⟨ A, hA ⟩ (f.invFun 0)]
        rw[h_f]

      _ = - |f ⟨ A, hA ⟩ - 0| + g (f.invFun 0) := by
        simp only [Equiv.invFun_as_coe, Equiv.apply_symm_apply, sub_zero]

      _ = - f ⟨ A, hA ⟩ + g (f.invFun 0) := by
        rw[abs_of_nonneg]
        simp only [sub_zero, Equiv.invFun_as_coe]
        simp only [sub_zero]
        exact right

    case inr =>
      calc
      g ⟨ A, hA ⟩ = g ⟨ A, hA ⟩ - g (f.invFun 0) + g (f.invFun 0) := by ring

      _ = |g ⟨ A, hA ⟩ - g (f.invFun 0)| + g (f.invFun 0) := by rw[abs_of_nonneg (sub_nonneg.mpr left)]

      _ = e.dist A (f.invFun 0) + g (f.invFun 0) := by
        rw[h_g]
        rw[P1'.eq_dist_eq_real l ⟨ A, hA ⟩ (f.invFun 0)]

      _ = |f ⟨ A, hA ⟩ - f (f.invFun 0)| + g (f.invFun 0) := by
        rw[P1.eq_dist_eq_real l ⟨ A, hA ⟩ (f.invFun 0)]
        rw[h_f]

      _ = |f ⟨ A, hA ⟩ - 0| + g (f.invFun 0) := by
        simp only [Equiv.invFun_as_coe, Equiv.apply_symm_apply, sub_zero]

      _ = - f ⟨ A, hA ⟩ + g (f.invFun 0) := by
        rw[abs_of_nonpos]
        simp only [sub_zero, Equiv.invFun_as_coe]
        simp only [sub_zero]
        exact right

theorem abcd' (l : e.Lines) (f : e.get_pts_of_line l ≃ ℝ ) (g : e.get_pts_of_line l ≃ ℝ ) (h_f : f = P1.to_real l) (h_g : g = P1'.to_real l) : ∀ A : e.get_pts_of_line l, g A = f A + g (f.invFun 0) ∨ g A = - (f A) + g (f.invFun 0) := by

  intro A

  by_cases h : (g A ≥ g (f.invFun 0)) ∧ (f A ≥ 0) ∨ (g A ≤ g (f.invFun 0) ∧ f A ≤ 0)
  case pos =>
    left
    exact (@abcd'' e P1 P1' l f g h_f h_g A).1 h

  case neg =>
    right
    have h' : (g A ≤  g (f.invFun 0)) ∧ (f A ≥ 0) ∨ (g A ≥  g (f.invFun 0) ∧ f A ≤ 0) := by
      push_neg at h
      -- By splitting into cases based on whether $g(A) \geq g(f^{-1}(0))$ or $g(A) \leq g(f^{-1}(0))$, we can derive the required disjunction.
      by_cases h_case : g A ≥ g (f.invFun 0);
      · -- Since $f(A) < 0$, we have $f(A) \leq 0$.
        right; exact ⟨h_case, by linarith [h.left h_case]⟩;
      · -- Since $g(A) < g(f.invFun 0)$, we have $g(A) \leq g(f.invFun 0)$ and $f(A) > 0$.
        left
        exact ⟨by linarith, by linarith [h.2 (by linarith)]⟩

    exact (@abcd'' e P1 P1' l f g h_f h_g A).2 h'


theorem ABCD (l : e.Lines) (f : e.get_pts_of_line l ≃ ℝ ) (g : e.get_pts_of_line l ≃ ℝ ) (h_f : f = P1.to_real l) (h_g : g = P1'.to_real l) : ∃ d : ℝ,  ∀ A : e.get_pts_of_line l, g A = f A + d ∨ g A = - (f A) + d
  := by
  use g (f.invFun 0)
  exact @abcd' e P1 P1' l f g h_f h_g

end PostulateOfLineMeasure

end Birkhoff
