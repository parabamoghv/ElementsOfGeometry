import Pythagoras.Geometry

open PlanarGeometry


namespace Garfield

structure RightTriangle_atC extends Triangle where
  h_right : Triangle.cos_angle B C A = 0


structure Construction (t : RightTriangle_atC) where
  A : d2 := t.A
  B : d2 := t.B
  C : d2 := t.C


  E : d2
  h_E_on_BC : E ∈ t.BCLine
  h_E_dist : dist C E = t.distBC + t.distCA ∧
             dist B E = t.distCA


  ED : Line := t.BCLine.mkPerp E
  D : d2
  h_D_on_ED : D ∈ ED
  h_D_dist : dist E D = t.distBC

  BED : Triangle
  h_BED : BED.A = B ∧ BED.B = E ∧ BED.C = D

  ABD : Triangle
  h_ABD : ABD.A = A ∧ ABD.B = B ∧ ABD.C = D

  ACED : Quadrilateral
  h_ACED : ACED.A = A ∧ ACED.B = C ∧ ACED.C = E ∧ ACED.D = D


lemma BED_area (t : RightTriangle_atC) (c : Construction t) :
  Triangle.area c.BED = (t.distBC * t.distCA) / 2 := by
  sorry


lemma ABD_area (t : RightTriangle_atC) (c : Construction t) :
  Triangle.area c.ABD = (t.distAB ^ 2) / 2 := by
  sorry


lemma ACED_area (t : RightTriangle_atC) (c : Construction t) :
  Quadrilateral.area c.ACED = (t.distBC + t.distCA)^2 / 2 := by
  sorry


theorem Pythagoras (t : Triangle) :
  t.distBC ^ 2 + t.distCA ^ 2 = t.distAB ^ 2 ↔
  Triangle.cos_angle t.B t.C t.A = 0
  := sorry


end Garfield
