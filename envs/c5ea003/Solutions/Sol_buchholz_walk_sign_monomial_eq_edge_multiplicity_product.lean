-- Prove2me | solution 1 for buchholz_walk_sign_monomial_eq_edge_multiplicity_product
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-24T00:01:47.307688+00:00
-- url     : https://prove2.me/submissions/af3cd444-0690-491c-8e19-823aff602632

import Definitions.Def_buchholz_signed_walk_sum

open MatrixCompletion
open scoped BigOperators

theorem solution
    {n n1 n2 : Nat}
    (eps : Finset (Fin n1 × Fin n2))
    (rows : Fin n → Fin n1) (cols : Fin n → Fin n2) :
    buchholzWalkSignMonomial eps rows cols =
      ∏ c : Fin n1 × Fin n2,
        rademacherSign eps c.1 c.2 ^
          buchholzEdgeMultiplicity rows cols c := by
  classical
  let Coord := Fin n1 × Fin n2
  let sgn : Coord → ℝ := fun c => rademacherSign eps c.1 c.2
  let f : Fin n → Coord := fun k => (rows k, cols k)
  let g : Fin n → Coord := fun k => (rows (buchholzCyclicSucc k), cols k)
  have hf :
      ∏ k : Fin n, sgn (f k) =
        ∏ c : Coord,
          sgn c ^ ((Finset.univ : Finset (Fin n)).filter (fun k => f k = c)).card := by
    symm
    calc
      ∏ c : Coord,
          sgn c ^ ((Finset.univ : Finset (Fin n)).filter (fun k => f k = c)).card
          =
        ∏ c : Coord,
          ∏ k ∈ (Finset.univ : Finset (Fin n)).filter (fun k => f k = c), sgn c := by
          apply Finset.prod_congr rfl
          intro c _hc
          rw [Finset.prod_const]
      _ = ∏ k : Fin n, sgn (f k) := by
          simpa using
            (Finset.prod_fiberwise' (s := (Finset.univ : Finset (Fin n)))
              (g := f) (f := sgn))
  have hg :
      ∏ k : Fin n, sgn (g k) =
        ∏ c : Coord,
          sgn c ^ ((Finset.univ : Finset (Fin n)).filter (fun k => g k = c)).card := by
    symm
    calc
      ∏ c : Coord,
          sgn c ^ ((Finset.univ : Finset (Fin n)).filter (fun k => g k = c)).card
          =
        ∏ c : Coord,
          ∏ k ∈ (Finset.univ : Finset (Fin n)).filter (fun k => g k = c), sgn c := by
          apply Finset.prod_congr rfl
          intro c _hc
          rw [Finset.prod_const]
      _ = ∏ k : Fin n, sgn (g k) := by
          simpa using
            (Finset.prod_fiberwise' (s := (Finset.univ : Finset (Fin n)))
              (g := g) (f := sgn))
  unfold buchholzWalkSignMonomial buchholzEdgeMultiplicity
  calc
    ∏ k : Fin n,
        (rademacherSign eps (rows k) (cols k) *
          rademacherSign eps (rows (buchholzCyclicSucc k)) (cols k))
        =
      (∏ k : Fin n, sgn (f k)) * (∏ k : Fin n, sgn (g k)) := by
        rw [Finset.prod_mul_distrib]
    _ =
      (∏ c : Coord,
          sgn c ^ ((Finset.univ : Finset (Fin n)).filter (fun k => f k = c)).card) *
        (∏ c : Coord,
          sgn c ^ ((Finset.univ : Finset (Fin n)).filter (fun k => g k = c)).card) := by
        rw [hf, hg]
    _ =
      ∏ c : Coord,
        sgn c ^
          (((Finset.univ : Finset (Fin n)).filter (fun k => f k = c)).card +
            ((Finset.univ : Finset (Fin n)).filter (fun k => g k = c)).card) := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro c _hc
        rw [pow_add]
    _ =
      ∏ c : Fin n1 × Fin n2,
        rademacherSign eps c.1 c.2 ^
          (((Finset.univ : Finset (Fin n)).filter
              (fun k => (rows k, cols k) = c)).card +
            ((Finset.univ : Finset (Fin n)).filter
              (fun k => (rows (buchholzCyclicSucc k), cols k) = c)).card) := by
        rfl
