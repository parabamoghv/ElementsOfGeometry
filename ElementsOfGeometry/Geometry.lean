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



/-- An abbrev for 2d euclidean space. Note that we use euclidean space rather than ℂ to allow
  for projection from 3d euclidean space -/
abbrev d2 := EuclideanSpace ℝ (Fin 2)


namespace PlanarGeometry


section LineDefinitions


/-- A simple line structure. We do not assume m≠ 0. -/
structure Line where
  m : d2
  c : d2
  -- non_degen : m ≠ 0

/--
  Point at time t: t • m + c
-/
def Line.position (l : Line) (t : ℝ) : d2 := t • l.m + l.c


/--
  The set of points that form the line.
-/
def Line.points (l : Line) : Set d2 :=
  {l.position t | t : ℝ}

/--
  Coersion of lint into d2
-/
instance : Coe (Line ) (Set d2) :=
  ⟨fun l => l.points⟩

/--
  checks if a point p lies on the line
-/
instance : Membership d2 (Line) :=
  ⟨fun l p => p ∈ (l : Set d2)⟩


/-- Turn two points into a line (this goes wrong if a = b) -/
def Line.ofPoints (a b : d2) : Line := ⟨b - a, a⟩

/--
  Turn slope and point to a line.
-/
def Line.ofSlopePoint (m c : d2) : Line := ⟨m, c ⟩

/-- Lines are parallel:
  Lines with slopes (M_x, M_y) and (M₂_x, M₂_y) are parallel if M_x/M_y = M₂_x / M₂_y
-/
def Line.isParallel (l l₂ : Line) : Prop :=
  let M_x: ℝ := l.m 0
  let M_y : ℝ := l.m 1
  let M2_x : ℝ := l₂.m 0
  let M2_y : ℝ := l₂.m 1
  -- true
  M2_x * M_y - M_x * M2_y = 0


/-- Lines are parallel:
  Lines with slopes (M_x, M_y) and (M₂_x, M₂_y) are perpendicular if M_x * M₂_x + M_y * M₂_y = 0
-/
def Line.isPerp (l l₂ : Line) :=
  inner ℝ l.m l₂.m = 0

/-- Make a perpendicular line through a point p -/
def Line.mkPerp (l : Line) (p : d2) : Line := ⟨!₂[-l.m 1, l.m 0], p⟩

/--
  Two lines are the same.
-/
def Line.eq (l l₂ : Line) : Prop :=
  (l : Set d2 ) = l₂

/--
  Line l intersects line l₂ at point p
-/
def Line.line_line_at (l l₂ : Line) (p : d2) : Prop :=  (l : Set d2) ∩ (l₂ : Set d2) = {p}


/--
  Line l intersects line l₂ if there is a point of intersection.
-/
def Line.is_line_line (l l₂ : Line) : Prop := ∃ p : d2, l.line_line_at l₂ p

/-- Reflect a point in a line -/
def Line.reflect (l : Line) (x : d2) := (2 * inner ℝ (x - l.c) l.m / inner ℝ l.m l.m) • l.m - x

/-- Reflect a set in a line -/
def Line.reflects (l : Line) (s : Set d2) := l.reflect '' s

/-- Reflect a line in another line -/
def Line.reflectl (l l₂ : Line) := Line.ofPoints (l.reflect l₂.c) (l.reflect (l₂.c + l₂.m))


end LineDefinitions

section CircleDefinitions

/--
  Circle in d2. We do not assume radius > 0.
-/
structure Circle where
  center : d2
  radius : ℝ

/--
  The set of points that form the circle
-/
def Circle.points (C : Circle) : Set d2 :=
  {x | dist x C.center = C.radius}


instance : Coe (Circle ) (Set d2) :=
  ⟨fun C => C.points⟩

/--
  Does the given point lie of the circle
-/
instance : Membership d2 (Circle) :=
  ⟨fun s p => p ∈ (s : Set d2)⟩

/--
  Does the given point lie in the interior of the circle
-/
def Circle.point_in_interior (C : Circle) (p : d2) : Prop := dist p C.center < C.radius

/--
  Does the given point lie in the exterior of the circle
-/
def Circle.point_in_exterior (C : Circle) (p : d2) : Prop := dist p C.center > C.radius

end CircleDefinitions


section CircleLine

/--
  The line l is tangent to the circle at point p
-/
def Circle.tangent_at (C : Circle) (l : Line) (p: d2) : Prop := (C : Set d2) ∩ (l : Set d2) = {p}

/--
  The line l is tangent to the circle
-/
def Circle.is_tangent (C : Circle) (l : Line) : Prop := ∃ p : d2, C.tangent_at l p

/--
  The line l intersects circle at p.
-/
def Circle.circle_line_at (C : Circle) (l : Line) (p : d2) : Prop := p ∈  (C : Set d2) ∩ (l : Set d2)

/--
  The line l intersects the circle
-/
def Circle.is_circle_line (C : Circle) (l : Line) : Prop := ∃ p : d2, C.circle_line_at l p

/--
  The line l is disjoint from the circle
-/
def Circle.is_disjoint_line (C : Circle) (l : Line) : Prop := (C : Set d2) ∩ (l : Set d2) = {}


end CircleLine


section CircleCircle

/--
  Two circles are tangent to each other at point p
-/
def Circle.tangent_circle_at (C C₁: Circle) (p: d2) : Prop := (C : Set d2) ∩ (C₁ : Set d2) = {p}

/--
  Two circles are tangent
-/
def Circle.is_tangent_circle (C C₁ : Circle) : Prop := ∃ p : d2, C.tangent_circle_at C₁ p

/--
  Circle C is internally tangent to the circle C₁ at P. That is, C and C₁ are tangent at P and C is internal to C₁
-/
def Circle.internal_tangent_circle_at (C C₁ : Circle) (p : d2) : Prop := C.tangent_circle_at C₁ p ∧ C₁.point_in_interior C.center

/--
  Circle C is internally tangent to the circle C₁. That is, C and C₁ are tangent and C is internal to C₁
-/
def Circle.is_internal_tangent_circle (C C₁ : Circle) : Prop := ∃ p : d2, C.internal_tangent_circle_at C₁ p

/--
  Circles are externally tangent to each other at P.
-/
def Circle.external_tangent_circle_at (C C₁ : Circle) (p : d2) : Prop := C.tangent_circle_at C₁ p ∧ C.point_in_exterior C₁.center

/--
  Circles are externally tangent.
-/
def Circle.is_external_tangent_circle (C C₁ : Circle) : Prop := ∃ p : d2, C.external_tangent_circle_at C₁ p

/--
  Circles intersect each other at p.
-/
def Circle.circle_circle_at (C C₁: Circle) (p : d2) : Prop := p ∈ (C : Set d2) ∩ (C₁ : Set d2)

/--
  circles intersect each other
-/
def Circle.is_circle_circle (C C₁ : Circle) : Prop := ∃ p : d2, C.circle_circle_at C₁ p

/--
  Circles are disjoint from each other.
-/
def Circle.is_disjoint_circle (C C₁ : Circle) : Prop := (C : Set d2) ∩ (C₁ : Set d2) = {}

end CircleCircle


section TriangleDefs

/-- A non-degenerate triangle -/
structure Triangle where
  A : d2
  B : d2
  C : d2
  h : AffineIndependent ℝ ![A, B, C]



/-- The midpoints of the sides -/
def Triangle.midBC (t : Triangle) := (1/2 : ℝ) • (t.B + t.C)

def Triangle.midCA (t : Triangle) := (1/2 : ℝ) • (t.C + t.A)

def Triangle.midAB (t : Triangle) := (1/2 : ℝ) • (t.A + t.B)

/-- The lengths of the triangle sides -/
def Triangle.distBC (t : Triangle) := dist t.B t.C

def Triangle.distCA (t : Triangle) := dist t.C t.A

def Triangle.distAB (t : Triangle) := dist t.A t.B

/-- Triangle s-distance -/
def Triangle.S (t : Triangle) := (1/2 : ℝ) * (t.distAB + t.distBC + t.distCA)

/-- Area of triangle using Heron formula -/
def Triangle.area (t : Triangle) : ℝ :=
  Real.sqrt (t.S * (t.S - t.distAB) * (t.S - t.distBC) * (t.S - t.distCA))

/-- The simplex associated with a triangle -/
def Triangle.simplex (t : Triangle) : Affine.Triangle ℝ d2 := ⟨_, t.h⟩

/-- The circumcenter of a triangle -/
def Triangle.circumcenter (t : Triangle) : d2 := t.simplex.circumcenter

/-- The circumradius of a triangle -/
def Triangle.circumradius (t : Triangle) := t.simplex.circumradius

/-- The circumcircle of a triangle -/
def Triangle.circumcircle (t : Triangle) : Circle := ⟨t.circumcenter, t.circumradius ⟩



/-- The orthocenter of the triangle -/
def Triangle.orthocenter (t : Triangle) := t.simplex.orthocenter

/-- The convex hull of the triangle -/
def Triangle.hull (t : Triangle) := convexHull ℝ {t.A, t.B, t.C}

/-- The triangle centroid -/
def Triangle.centroid (t : Triangle) := (1/3 : ℝ) • (t.A + t.B + t.C)

/-- The triangle weighted sum. -/
def Triangle.weighted_sum (t : Triangle) (wa wb wc : ℝ) :=
    (wa * t.distBC + wb * t.distCA + wc * t.distAB) •
    ((wa * t.distBC) • t.A + (wb * t.distCA) • t.B + (wc * t.distAB) • t.C)

/-- The triangle incenter. See https://en.wikipedia.org/wiki/Incircle_and_excircles -/
def Triangle.incenter (t : Triangle) := t.weighted_sum (1/(t.distBC + t.distCA + t.distAB)) (1/(t.distBC + t.distCA + t.distAB)) (1/(t.distBC + t.distCA + t.distAB))

/-- The triangle excenters -/
def Triangle.excenterA (t : Triangle) := t.weighted_sum (-1) 1 1

def Triangle.excenterB (t : Triangle) := t.weighted_sum 1 (-1) 1

def Triangle.excenterC (t : Triangle) := t.weighted_sum 1 1 (-1)


def Triangle.inradius (t : Triangle) : ℝ :=
  Real.sqrt ( (t.S - t.distAB) * (t.S - t.distBC) * (t.S - t.distCA) / t.S )


def Triangle.incircle (t : Triangle) : Circle := ⟨ t.incenter, t.inradius ⟩


/-- The lines corresponding to side lengths -/
def Triangle.ABLine (t : Triangle) := Line.ofPoints t.A t.B

def Triangle.BCLine (t : Triangle) := Line.ofPoints t.B t.C

def Triangle.CALine (t : Triangle) := Line.ofPoints t.C t.A


/--
  angle bisector line of angle ABC. (note: ABC must be affine independent but we do not enforce it here).
  Let <m, c> be the angle bisector. Then,
  m · (a - b) / |a - b| = m · (c - b) / |c - b|.
  Simplify
  m · ((a-b)/|a-b| - (c-b)/|c-b|) = 0.
  Let m' =   ((a-b)/|a-b| - (c-b)/|c-b|).
  Angle bisector is the line perpendicular to m'.
-/
def Triangle.angleBisector (A B C : d2) : Line :=
  let m' : d2 := ( 1 / dist A B ) • ( A - B ) - ( 1/ dist C B) • ( C - B )
  let l' : Line := Line.mk m' B

  l'.mkPerp B


/--
  Cosine of the angle ABC
-/
def Triangle.cos_angle (A B C : d2) : ℝ :=
  let BA := A - B
  let BC := C - B
  (inner ℝ BA BC / (‖BA‖ * ‖BC‖))

/--
  Sine of the angle ABC. Angle is oriented from BA to BC. Anticlockwise is positive.
-/
def Triangle.sin_angle (A B C : d2) : ℝ :=
  let BA := A - B
  let BC := C - B
  let cross := BA 0 * BC 1 - BA 1 * BC 0
  cross / (‖BA‖ * ‖BC‖)



/--
  Checks if the point P is on the segment A B
-/
def Line.onSegmentAB (P A B : d2) : Prop :=
  Triangle.cos_angle P A B = 1 ∧ Triangle.cos_angle P B A = 1


/--
  Checks if the point P is on the segment from t=0 to t=1 of the line
-/
def Line.onSegment (l : Line) (P : d2) : Prop :=
  Line.onSegmentAB P (l.position 0) (l.position 1)


end TriangleDefs



section SegmentDefs


structure Segment where
  A : d2
  B : d2
  h_uniqe : A 0 ≤ B 0 ∨ (A 0 = B 0 ∧ A 1 ≤ B 1) -- Enforcing lexicographic order to ensure uniqueness
deriving DecidableEq


def Segment.length (s : Segment) : ℝ := dist s.A s.B


def Segment.toLine (s : Segment) : Line := Line.ofPoints s.A s.B


/--
  Point at time t: t • m + c
-/
def Segment.position (s : Segment) (t : ℝ) : d2 := s.toLine.position t


/--
  The set of points that form the segment.
-/
def Segment.points (s : Segment) : Set d2 :=
  {s.position t | t : unitInterval }

/--
  Coersion of segment into set of points
-/
instance : Coe (Segment) (Set d2) :=
  ⟨fun s => s.points⟩

/--
  checks if a point p lies on the segment
-/
instance : Membership d2 (Segment) :=
  ⟨fun s p => p ∈ (s : Set d2)⟩

/--
  Checks if the point p lies on the segment
-/
def Segment.containsPoint (s : Segment) (p : d2) : Prop :=
  p ∈ s

def Segment.segment_line_at (s : Segment) (l : Line) (p : d2) : Prop :=
  p ∈ s ∧ p ∈ l

def Segment.is_segment_line (s : Segment) (l : Line) : Prop :=
  ∃ p : d2, s.segment_line_at l p




end SegmentDefs

section QuadrilateralDefinitions

/--
  Simple quadrilateral structure. Note that we do not enforce that it is convex
-/
structure Quadrilateral where
  A : d2
  B : d2
  C : d2
  D : d2
  h : AffineIndependent ℝ ![A, B, C, D]

/--
  The line AB of the quadrilateral
-/
def Quadrilateral.lineAB (q : Quadrilateral) : Line :=
  Line.ofPoints q.A q.B

/--
  The line BC of the quadrilateral
-/
def Quadrilateral.lineBC (q : Quadrilateral) : Line :=
  Line.ofPoints q.B q.C


/--
  The line CD of the quadrilateral
-/
def Quadrilateral.lineCD (q : Quadrilateral) : Line :=
  Line.ofPoints q.C q.D

/--
  The line DA of the quadrilateral
-/
def Quadrilateral.lineDA (q : Quadrilateral) : Line :=
  Line.ofPoints q.D q.A

/--
  The diagonal line AC of the quadrilateral
-/
def Quadrilateral.lineAC (q : Quadrilateral) : Line :=
  Line.ofPoints q.A q.C

/--
  The diagonal line BD of the quadrilateral
-/
def Quadrilateral.lineBD (q : Quadrilateral) : Line :=
  Line.ofPoints q.B q.D

def Quadrilateral.triangle (q : Quadrilateral) (f : Fin 3 ↪ Fin 4) : Triangle := by
  constructor
  case A => exact ![q.A, q.B, q.C, q.D] (f 0)
  case B => exact ![q.A, q.B, q.C, q.D] (f 1)
  case C => exact ![q.A, q.B, q.C, q.D] (f 2)

  case h =>
    -- Since $f$ is injective, the four points are distinct, and by hypothesis, they are affinely independent. Therefore, any three of them are also affinely independent.
    have h_affine_indep : AffineIndependent ℝ ![q.A, q.B, q.C, q.D] := by
      exact q.h;
    -- Since the four points are affinely independent, any subset of them is also affinely independent.
    have h_subset : ∀ (s : Finset (Fin 4)), s.card = 3 → AffineIndependent ℝ (fun i : s => ![q.A, q.B, q.C, q.D] i) := by
      intros s hs_card
      have h_subset : s ⊆ Finset.univ := by
        exact Finset.subset_univ s;
      convert h_affine_indep.comp_embedding _ _ using 1;
      any_goals exact Finset.univ.image ( fun x : { x : Fin 4 // x ∈ s } => x );
      rw [ affineIndependent_iff_of_fintype ];
      norm_num +zetaDelta at *;
      swap;
      exact ⟨ fun x => x, fun x y hxy => by simpa [ Subtype.ext_iff ] using hxy ⟩;
      rfl;
    have h_subset : AffineIndependent ℝ (fun i : Fin 3 => ![q.A, q.B, q.C, q.D] (f i)) := by
      -- Since the image of f is a subset of size 3, we can apply h_subset to this subset.
      have h_image : Finset.card (Finset.image f Finset.univ) = 3 := by
        exact Finset.card_image_of_injective _ f.injective;
      convert h_subset ( Finset.image f Finset.univ ) h_image using 1;
      bound;
      · convert h_subset ( Finset.image f Finset.univ ) h_image using 1;
      · convert a.comp_embedding ( show Fin 3 ↪ { x : Fin 4 // x ∈ Finset.image f Finset.univ } from ⟨ fun i => ⟨ f i, Finset.mem_image_of_mem _ ( Finset.mem_univ _ ) ⟩, fun i j hij => by simpa [ Fin.ext_iff ] using hij ⟩ ) using 1;
    -- Since $f$ is injective, the image of $f$ is a subset of $\{0, 1, 2, 3\}$ with three elements. Therefore, the points selected by $f$ are exactly the points in the list $[q.A, q.B, q.C, q.D]$ at positions $f 0$, $f 1$, and $f 2$.
    have h_image : ∀ i : Fin 3, ![q.A, q.B, q.C, q.D] (f i) = if f i = 0 then q.A else if f i = 1 then q.B else if f i = 2 then q.C else q.D := by
      intro i; rcases f i with ( _ | _ | _ | _ | i ) <;> trivial;
    convert h_subset using 1;
    ext i; fin_cases i <;> simp +decide [ h_image ] ;


def Quadrilateral.triangleABC (q : Quadrilateral) : Triangle :=
  let f : Fin 3 ↪ Fin 4 := by
      constructor
      case toFun =>
        exact fun
          | 0 => 0
          | 1 => 1
          | 2 => 2

      case inj' =>
        decide +kernel

  q.triangle f


def Quadrilateral.triangleBCD (q : Quadrilateral) : Triangle :=
  let f : Fin 3 ↪ Fin 4 := by
      constructor
      case toFun =>
        exact fun
          | 0 => 1
          | 1 => 2
          | 2 => 3

      case inj' =>
        -- To prove injectivity, we can check all pairs of elements in Fin 3.
        intro x y hxy
        fin_cases x <;> fin_cases y <;> simp +decide at hxy ⊢

    q.triangle f


def Quadrilateral.triangleCDA (q : Quadrilateral) : Triangle :=
  let f : Fin 3 ↪ Fin 4 := by
      constructor
      case toFun =>
        exact fun
          | 0 => 2
          | 1 => 3
          | 2 => 0

      case inj' =>
        decide +revert

  q.triangle f


def Quadrilateral.triangleDAB (q : Quadrilateral) : Triangle :=
  let f : Fin 3 ↪ Fin 4 := by
      constructor
      case toFun =>
        exact fun
          | 0 => 3
          | 1 => 0
          | 2 => 1

      case inj' =>
        decide +revert

  q.triangle f



/--
  Area of the quadrilateral : Area of the compoent triangles
-/
def Quadrilateral.area (q : Quadrilateral) : ℝ := q.triangleABC.area + q.triangleCDA.area


/--
  A convex quadrilateral: Each orientation
  AD → AB
  BA → BC
  CB →ₗ CD
  DC → DA
  is all clockwise or all anticlockwise.
-/
structure ConvexQuadrilateral extends Quadrilateral where

  convex : (Triangle.sin_angle D A B > 0 ∧ Triangle.sin_angle A B C > 0 ∧ Triangle.sin_angle B C D > 0 ∧ Triangle.sin_angle C D A > 0) ∨
                     (Triangle.sin_angle D A B < 0 ∧ Triangle.sin_angle A B C < 0 ∧ Triangle.sin_angle B C D < 0 ∧ Triangle.sin_angle C D A < 0)




/--
  A convex quadrilateral': A quadrilateral where the diagonals intersect and the intersection point is between the vertices (i.e. on the diagonal segments).
-/
structure ConvexQuadrilateral' extends Quadrilateral where

  diagonals_intersect : let AC := Line.ofPoints A C
                        let BD := Line.ofPoints B D
                        AC.is_line_line BD
  convex : let AC := Line.ofPoints A C
           let BD := Line.ofPoints B D
          ∃ P : d2, AC.line_line_at BD P ∧ AC.onSegment P ∧ BD.onSegment P



end QuadrilateralDefinitions

theorem problem : 2 + 2 = 5 := by sorry

end PlanarGeometry
