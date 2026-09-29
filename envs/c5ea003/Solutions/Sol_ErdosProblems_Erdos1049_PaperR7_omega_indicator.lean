-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR7.omega_indicator
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:42:42.55392+00:00
-- url     : https://prove2.me/submissions/4056d3df-3f59-4ae9-80bd-f48db39f252a

import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

   
                                                      

                                                                      
                                                                           
                                                                           
                                                                          
                                                  
  

namespace ErdosProblems.Erdos1049.PaperR7
private theorem floor_from_bounds (x : ℝ) (c : ℝ) (k : ℤ)
    (hl : (k : ℝ) ≤ c * x) (hu : c * x < (k : ℝ) + 1) :
    ⌊c * x⌋ = k := Int.floor_eq_iff.mpr ⟨hl, hu⟩

private theorem omega_cell_00 (x : ℝ)
    (hl : (0 : ℝ) ≤ x) (hu : x < (1 : ℝ) / 15) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (0 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (0 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (0 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (0 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 0 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : ¬ InOmegaSupport x := by
    intro hs
    unfold InOmegaSupport at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    all_goals rcases ‹_ ∧ _› with ⟨hlo, hhi⟩
    all_goals linarith
  refine ⟨Or.inl hw, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    exact (hs h).elim

private theorem omega_cell_01 (x : ℝ)
    (hl : (1 : ℝ) / 15 ≤ x) (hu : x < (1 : ℝ) / 14) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (0 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (0 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (0 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (1 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 0 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : ¬ InOmegaSupport x := by
    intro hs
    unfold InOmegaSupport at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    all_goals rcases ‹_ ∧ _› with ⟨hlo, hhi⟩
    all_goals linarith
  refine ⟨Or.inl hw, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    exact (hs h).elim

private theorem omega_cell_02 (x : ℝ)
    (hl : (1 : ℝ) / 14 ≤ x) (hu : x < (1 : ℝ) / 13) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (0 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (0 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (1 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (1 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 1 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : InOmegaSupport x := by
    unfold InOmegaSupport
    left
    constructor <;> linarith
  exact ⟨Or.inr hw, ⟨fun _ => hs, fun _ => hw⟩⟩

private theorem omega_cell_03 (x : ℝ)
    (hl : (1 : ℝ) / 13 ≤ x) (hu : x < (1 : ℝ) / 12) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (0 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (1 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (1 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (1 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 1 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : InOmegaSupport x := by
    unfold InOmegaSupport
    left
    constructor <;> linarith
  exact ⟨Or.inr hw, ⟨fun _ => hs, fun _ => hw⟩⟩

private theorem omega_cell_04 (x : ℝ)
    (hl : (1 : ℝ) / 12 ≤ x) (hu : x < (2 : ℝ) / 15) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (1 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (1 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (1 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (1 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 0 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : ¬ InOmegaSupport x := by
    intro hs
    unfold InOmegaSupport at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    all_goals rcases ‹_ ∧ _› with ⟨hlo, hhi⟩
    all_goals linarith
  refine ⟨Or.inl hw, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    exact (hs h).elim

private theorem omega_cell_05 (x : ℝ)
    (hl : (2 : ℝ) / 15 ≤ x) (hu : x < (1 : ℝ) / 7) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (1 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (1 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (1 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (2 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 0 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : ¬ InOmegaSupport x := by
    intro hs
    unfold InOmegaSupport at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    all_goals rcases ‹_ ∧ _› with ⟨hlo, hhi⟩
    all_goals linarith
  refine ⟨Or.inl hw, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    exact (hs h).elim

private theorem omega_cell_06 (x : ℝ)
    (hl : (1 : ℝ) / 7 ≤ x) (hu : x < (2 : ℝ) / 13) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (1 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (1 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (2 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (2 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 1 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : InOmegaSupport x := by
    unfold InOmegaSupport
    right
    left
    constructor <;> linarith
  exact ⟨Or.inr hw, ⟨fun _ => hs, fun _ => hw⟩⟩

private theorem omega_cell_07 (x : ℝ)
    (hl : (2 : ℝ) / 13 ≤ x) (hu : x < (1 : ℝ) / 6) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (1 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (2 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (2 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (2 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 1 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : InOmegaSupport x := by
    unfold InOmegaSupport
    right
    left
    constructor <;> linarith
  exact ⟨Or.inr hw, ⟨fun _ => hs, fun _ => hw⟩⟩

private theorem omega_cell_08 (x : ℝ)
    (hl : (1 : ℝ) / 6 ≤ x) (hu : x < (1 : ℝ) / 5) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (2 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (2 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (2 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (2 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 0 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : ¬ InOmegaSupport x := by
    intro hs
    unfold InOmegaSupport at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    all_goals rcases ‹_ ∧ _› with ⟨hlo, hhi⟩
    all_goals linarith
  refine ⟨Or.inl hw, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    exact (hs h).elim

private theorem omega_cell_09 (x : ℝ)
    (hl : (1 : ℝ) / 5 ≤ x) (hu : x < (3 : ℝ) / 14) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (2 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (2 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (2 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (3 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 0 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : ¬ InOmegaSupport x := by
    intro hs
    unfold InOmegaSupport at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    all_goals rcases ‹_ ∧ _› with ⟨hlo, hhi⟩
    all_goals linarith
  refine ⟨Or.inl hw, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    exact (hs h).elim

private theorem omega_cell_10 (x : ℝ)
    (hl : (3 : ℝ) / 14 ≤ x) (hu : x < (3 : ℝ) / 13) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (2 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (2 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (3 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (3 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 1 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : InOmegaSupport x := by
    unfold InOmegaSupport
    right
    right
    left
    constructor <;> linarith
  exact ⟨Or.inr hw, ⟨fun _ => hs, fun _ => hw⟩⟩

private theorem omega_cell_11 (x : ℝ)
    (hl : (3 : ℝ) / 13 ≤ x) (hu : x < (1 : ℝ) / 4) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (2 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (3 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (3 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (3 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 1 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : InOmegaSupport x := by
    unfold InOmegaSupport
    right
    right
    left
    constructor <;> linarith
  exact ⟨Or.inr hw, ⟨fun _ => hs, fun _ => hw⟩⟩

private theorem omega_cell_12 (x : ℝ)
    (hl : (1 : ℝ) / 4 ≤ x) (hu : x < (4 : ℝ) / 15) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (3 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (3 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (3 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (3 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 0 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : ¬ InOmegaSupport x := by
    intro hs
    unfold InOmegaSupport at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    all_goals rcases ‹_ ∧ _› with ⟨hlo, hhi⟩
    all_goals linarith
  refine ⟨Or.inl hw, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    exact (hs h).elim

private theorem omega_cell_13 (x : ℝ)
    (hl : (4 : ℝ) / 15 ≤ x) (hu : x < (2 : ℝ) / 7) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (3 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (3 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (3 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (4 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 0 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : ¬ InOmegaSupport x := by
    intro hs
    unfold InOmegaSupport at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    all_goals rcases ‹_ ∧ _› with ⟨hlo, hhi⟩
    all_goals linarith
  refine ⟨Or.inl hw, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    exact (hs h).elim

private theorem omega_cell_14 (x : ℝ)
    (hl : (2 : ℝ) / 7 ≤ x) (hu : x < (4 : ℝ) / 13) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (3 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (3 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (4 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (4 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 1 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : InOmegaSupport x := by
    unfold InOmegaSupport
    right
    right
    right
    left
    constructor <;> linarith
  exact ⟨Or.inr hw, ⟨fun _ => hs, fun _ => hw⟩⟩

private theorem omega_cell_15 (x : ℝ)
    (hl : (4 : ℝ) / 13 ≤ x) (hu : x < (1 : ℝ) / 3) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (3 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (4 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (4 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (4 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 1 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : InOmegaSupport x := by
    unfold InOmegaSupport
    right
    right
    right
    left
    constructor <;> linarith
  exact ⟨Or.inr hw, ⟨fun _ => hs, fun _ => hw⟩⟩

private theorem omega_cell_16 (x : ℝ)
    (hl : (1 : ℝ) / 3 ≤ x) (hu : x < (5 : ℝ) / 14) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (4 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (4 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (4 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (5 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 0 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : ¬ InOmegaSupport x := by
    intro hs
    unfold InOmegaSupport at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    all_goals rcases ‹_ ∧ _› with ⟨hlo, hhi⟩
    all_goals linarith
  refine ⟨Or.inl hw, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    exact (hs h).elim

private theorem omega_cell_17 (x : ℝ)
    (hl : (5 : ℝ) / 14 ≤ x) (hu : x < (5 : ℝ) / 13) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (4 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (4 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (5 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (5 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 1 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : InOmegaSupport x := by
    unfold InOmegaSupport
    right
    right
    right
    right
    left
    constructor <;> linarith
  exact ⟨Or.inr hw, ⟨fun _ => hs, fun _ => hw⟩⟩

private theorem omega_cell_18 (x : ℝ)
    (hl : (5 : ℝ) / 13 ≤ x) (hu : x < (2 : ℝ) / 5) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (4 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (5 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (5 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (5 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 1 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : InOmegaSupport x := by
    unfold InOmegaSupport
    right
    right
    right
    right
    left
    constructor <;> linarith
  exact ⟨Or.inr hw, ⟨fun _ => hs, fun _ => hw⟩⟩

private theorem omega_cell_19 (x : ℝ)
    (hl : (2 : ℝ) / 5 ≤ x) (hu : x < (5 : ℝ) / 12) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (4 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (5 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (5 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (6 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 0 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : ¬ InOmegaSupport x := by
    intro hs
    unfold InOmegaSupport at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    all_goals rcases ‹_ ∧ _› with ⟨hlo, hhi⟩
    all_goals linarith
  refine ⟨Or.inl hw, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    exact (hs h).elim

private theorem omega_cell_20 (x : ℝ)
    (hl : (5 : ℝ) / 12 ≤ x) (hu : x < (3 : ℝ) / 7) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (5 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (5 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (5 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (6 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 0 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : ¬ InOmegaSupport x := by
    intro hs
    unfold InOmegaSupport at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    all_goals rcases ‹_ ∧ _› with ⟨hlo, hhi⟩
    all_goals linarith
  refine ⟨Or.inl hw, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    exact (hs h).elim

private theorem omega_cell_21 (x : ℝ)
    (hl : (3 : ℝ) / 7 ≤ x) (hu : x < (6 : ℝ) / 13) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (5 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (5 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (6 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (6 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 1 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : InOmegaSupport x := by
    unfold InOmegaSupport
    right
    right
    right
    right
    right
    left
    constructor <;> linarith
  exact ⟨Or.inr hw, ⟨fun _ => hs, fun _ => hw⟩⟩

private theorem omega_cell_22 (x : ℝ)
    (hl : (6 : ℝ) / 13 ≤ x) (hu : x < (7 : ℝ) / 15) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (5 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (6 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (6 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (6 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 1 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : InOmegaSupport x := by
    unfold InOmegaSupport
    right
    right
    right
    right
    right
    left
    constructor <;> linarith
  exact ⟨Or.inr hw, ⟨fun _ => hs, fun _ => hw⟩⟩

private theorem omega_cell_23 (x : ℝ)
    (hl : (7 : ℝ) / 15 ≤ x) (hu : x < (1 : ℝ) / 2) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (5 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (6 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (6 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (7 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 0 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : ¬ InOmegaSupport x := by
    intro hs
    unfold InOmegaSupport at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    all_goals rcases ‹_ ∧ _› with ⟨hlo, hhi⟩
    all_goals linarith
  refine ⟨Or.inl hw, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    exact (hs h).elim

private theorem omega_cell_24 (x : ℝ)
    (hl : (1 : ℝ) / 2 ≤ x) (hu : x < (8 : ℝ) / 15) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (6 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (6 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (7 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (7 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 1 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : InOmegaSupport x := by
    unfold InOmegaSupport
    right
    right
    right
    right
    right
    right
    left
    constructor <;> linarith
  exact ⟨Or.inr hw, ⟨fun _ => hs, fun _ => hw⟩⟩

private theorem omega_cell_25 (x : ℝ)
    (hl : (8 : ℝ) / 15 ≤ x) (hu : x < (7 : ℝ) / 13) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (6 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (6 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (7 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (8 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 0 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : ¬ InOmegaSupport x := by
    intro hs
    unfold InOmegaSupport at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    all_goals rcases ‹_ ∧ _› with ⟨hlo, hhi⟩
    all_goals linarith
  refine ⟨Or.inl hw, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    exact (hs h).elim

private theorem omega_cell_26 (x : ℝ)
    (hl : (7 : ℝ) / 13 ≤ x) (hu : x < (4 : ℝ) / 7) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (6 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (7 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (7 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (8 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 0 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : ¬ InOmegaSupport x := by
    intro hs
    unfold InOmegaSupport at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    all_goals rcases ‹_ ∧ _› with ⟨hlo, hhi⟩
    all_goals linarith
  refine ⟨Or.inl hw, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    exact (hs h).elim

private theorem omega_cell_27 (x : ℝ)
    (hl : (4 : ℝ) / 7 ≤ x) (hu : x < (7 : ℝ) / 12) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (6 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (7 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (8 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (8 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 1 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : InOmegaSupport x := by
    unfold InOmegaSupport
    right
    right
    right
    right
    right
    right
    right
    left
    constructor <;> linarith
  exact ⟨Or.inr hw, ⟨fun _ => hs, fun _ => hw⟩⟩

private theorem omega_cell_28 (x : ℝ)
    (hl : (7 : ℝ) / 12 ≤ x) (hu : x < (3 : ℝ) / 5) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (7 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (7 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (8 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (8 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 1 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : InOmegaSupport x := by
    unfold InOmegaSupport
    right
    right
    right
    right
    right
    right
    right
    left
    constructor <;> linarith
  exact ⟨Or.inr hw, ⟨fun _ => hs, fun _ => hw⟩⟩

private theorem omega_cell_29 (x : ℝ)
    (hl : (3 : ℝ) / 5 ≤ x) (hu : x < (8 : ℝ) / 13) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (7 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (7 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (8 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (9 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 0 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : ¬ InOmegaSupport x := by
    intro hs
    unfold InOmegaSupport at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    all_goals rcases ‹_ ∧ _› with ⟨hlo, hhi⟩
    all_goals linarith
  refine ⟨Or.inl hw, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    exact (hs h).elim

private theorem omega_cell_30 (x : ℝ)
    (hl : (8 : ℝ) / 13 ≤ x) (hu : x < (9 : ℝ) / 14) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (7 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (8 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (8 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (9 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 0 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : ¬ InOmegaSupport x := by
    intro hs
    unfold InOmegaSupport at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    all_goals rcases ‹_ ∧ _› with ⟨hlo, hhi⟩
    all_goals linarith
  refine ⟨Or.inl hw, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    exact (hs h).elim

private theorem omega_cell_31 (x : ℝ)
    (hl : (9 : ℝ) / 14 ≤ x) (hu : x < (2 : ℝ) / 3) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (7 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (8 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (9 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (9 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 1 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : InOmegaSupport x := by
    unfold InOmegaSupport
    right
    right
    right
    right
    right
    right
    right
    right
    left
    constructor <;> linarith
  exact ⟨Or.inr hw, ⟨fun _ => hs, fun _ => hw⟩⟩

private theorem omega_cell_32 (x : ℝ)
    (hl : (2 : ℝ) / 3 ≤ x) (hu : x < (9 : ℝ) / 13) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (8 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (8 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (9 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (10 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 0 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : ¬ InOmegaSupport x := by
    intro hs
    unfold InOmegaSupport at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    all_goals rcases ‹_ ∧ _› with ⟨hlo, hhi⟩
    all_goals linarith
  refine ⟨Or.inl hw, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    exact (hs h).elim

private theorem omega_cell_33 (x : ℝ)
    (hl : (9 : ℝ) / 13 ≤ x) (hu : x < (5 : ℝ) / 7) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (8 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (9 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (9 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (10 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 0 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : ¬ InOmegaSupport x := by
    intro hs
    unfold InOmegaSupport at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    all_goals rcases ‹_ ∧ _› with ⟨hlo, hhi⟩
    all_goals linarith
  refine ⟨Or.inl hw, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    exact (hs h).elim

private theorem omega_cell_34 (x : ℝ)
    (hl : (5 : ℝ) / 7 ≤ x) (hu : x < (11 : ℝ) / 15) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (8 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (9 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (10 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (10 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 1 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : InOmegaSupport x := by
    unfold InOmegaSupport
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    constructor <;> linarith
  exact ⟨Or.inr hw, ⟨fun _ => hs, fun _ => hw⟩⟩

private theorem omega_cell_35 (x : ℝ)
    (hl : (11 : ℝ) / 15 ≤ x) (hu : x < (3 : ℝ) / 4) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (8 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (9 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (10 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (11 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 0 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : ¬ InOmegaSupport x := by
    intro hs
    unfold InOmegaSupport at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    all_goals rcases ‹_ ∧ _› with ⟨hlo, hhi⟩
    all_goals linarith
  refine ⟨Or.inl hw, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    exact (hs h).elim

private theorem omega_cell_36 (x : ℝ)
    (hl : (3 : ℝ) / 4 ≤ x) (hu : x < (10 : ℝ) / 13) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (9 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (9 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (10 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (11 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 0 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : ¬ InOmegaSupport x := by
    intro hs
    unfold InOmegaSupport at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    all_goals rcases ‹_ ∧ _› with ⟨hlo, hhi⟩
    all_goals linarith
  refine ⟨Or.inl hw, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    exact (hs h).elim

private theorem omega_cell_37 (x : ℝ)
    (hl : (10 : ℝ) / 13 ≤ x) (hu : x < (11 : ℝ) / 14) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (9 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (10 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (10 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (11 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 0 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : ¬ InOmegaSupport x := by
    intro hs
    unfold InOmegaSupport at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    all_goals rcases ‹_ ∧ _› with ⟨hlo, hhi⟩
    all_goals linarith
  refine ⟨Or.inl hw, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    exact (hs h).elim

private theorem omega_cell_38 (x : ℝ)
    (hl : (11 : ℝ) / 14 ≤ x) (hu : x < (4 : ℝ) / 5) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (9 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (10 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (11 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (11 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 1 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : InOmegaSupport x := by
    unfold InOmegaSupport
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    constructor <;> linarith
  exact ⟨Or.inr hw, ⟨fun _ => hs, fun _ => hw⟩⟩

private theorem omega_cell_39 (x : ℝ)
    (hl : (4 : ℝ) / 5 ≤ x) (hu : x < (5 : ℝ) / 6) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (9 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (10 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (11 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (12 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 0 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : ¬ InOmegaSupport x := by
    intro hs
    unfold InOmegaSupport at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    all_goals rcases ‹_ ∧ _› with ⟨hlo, hhi⟩
    all_goals linarith
  refine ⟨Or.inl hw, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    exact (hs h).elim

private theorem omega_cell_40 (x : ℝ)
    (hl : (5 : ℝ) / 6 ≤ x) (hu : x < (11 : ℝ) / 13) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (10 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (10 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (11 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (12 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 0 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : ¬ InOmegaSupport x := by
    intro hs
    unfold InOmegaSupport at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    all_goals rcases ‹_ ∧ _› with ⟨hlo, hhi⟩
    all_goals linarith
  refine ⟨Or.inl hw, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    exact (hs h).elim

private theorem omega_cell_41 (x : ℝ)
    (hl : (11 : ℝ) / 13 ≤ x) (hu : x < (6 : ℝ) / 7) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (10 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (11 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (11 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (12 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 0 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : ¬ InOmegaSupport x := by
    intro hs
    unfold InOmegaSupport at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    all_goals rcases ‹_ ∧ _› with ⟨hlo, hhi⟩
    all_goals linarith
  refine ⟨Or.inl hw, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    exact (hs h).elim

private theorem omega_cell_42 (x : ℝ)
    (hl : (6 : ℝ) / 7 ≤ x) (hu : x < (13 : ℝ) / 15) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (10 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (11 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (12 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (12 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 1 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : InOmegaSupport x := by
    unfold InOmegaSupport
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    constructor <;> linarith
  exact ⟨Or.inr hw, ⟨fun _ => hs, fun _ => hw⟩⟩

private theorem omega_cell_43 (x : ℝ)
    (hl : (13 : ℝ) / 15 ≤ x) (hu : x < (11 : ℝ) / 12) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (10 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (11 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (12 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (13 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 0 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : ¬ InOmegaSupport x := by
    intro hs
    unfold InOmegaSupport at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    all_goals rcases ‹_ ∧ _› with ⟨hlo, hhi⟩
    all_goals linarith
  refine ⟨Or.inl hw, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    exact (hs h).elim

private theorem omega_cell_44 (x : ℝ)
    (hl : (11 : ℝ) / 12 ≤ x) (hu : x < (12 : ℝ) / 13) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (11 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (11 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (12 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (13 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 0 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : ¬ InOmegaSupport x := by
    intro hs
    unfold InOmegaSupport at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    all_goals rcases ‹_ ∧ _› with ⟨hlo, hhi⟩
    all_goals linarith
  refine ⟨Or.inl hw, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    exact (hs h).elim

private theorem omega_cell_45 (x : ℝ)
    (hl : (12 : ℝ) / 13 ≤ x) (hu : x < (13 : ℝ) / 14) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (11 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (12 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (12 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (13 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 0 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : ¬ InOmegaSupport x := by
    intro hs
    unfold InOmegaSupport at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    all_goals rcases ‹_ ∧ _› with ⟨hlo, hhi⟩
    all_goals linarith
  refine ⟨Or.inl hw, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    exact (hs h).elim

private theorem omega_cell_46 (x : ℝ)
    (hl : (13 : ℝ) / 14 ≤ x) (hu : x < (14 : ℝ) / 15) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (11 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (12 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (13 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (13 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 1 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : InOmegaSupport x := by
    unfold InOmegaSupport
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    constructor <;> linarith
  exact ⟨Or.inr hw, ⟨fun _ => hs, fun _ => hw⟩⟩

private theorem omega_cell_47 (x : ℝ)
    (hl : (14 : ℝ) / 15 ≤ x) (hu : x < (1 : ℝ)) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  have h12 : ⌊(12 : ℝ) * x⌋ = (11 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h13 : ⌊(13 : ℝ) * x⌋ = (12 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h14 : ⌊(14 : ℝ) * x⌋ = (13 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have h15 : ⌊(15 : ℝ) * x⌋ = (14 : ℤ) := by
    apply floor_from_bounds <;> norm_num <;> linarith
  have hw : omegaWeight x = 0 := by
    norm_num [omegaWeight, h12, h13, h14, h15]
  have hs : ¬ InOmegaSupport x := by
    intro hs
    unfold InOmegaSupport at hs
    rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    all_goals rcases ‹_ ∧ _› with ⟨hlo, hhi⟩
    all_goals linarith
  refine ⟨Or.inl hw, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    exact (hs h).elim
end ErdosProblems.Erdos1049.PaperR7

open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR7 in
theorem solution (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  by_cases h0 : x < (1 : ℝ) / 15
  · exact omega_cell_00 x hx0 h0
  by_cases h1 : x < (1 : ℝ) / 14
  · exact omega_cell_01 x (le_of_not_gt h0) h1
  by_cases h2 : x < (1 : ℝ) / 13
  · exact omega_cell_02 x (le_of_not_gt h1) h2
  by_cases h3 : x < (1 : ℝ) / 12
  · exact omega_cell_03 x (le_of_not_gt h2) h3
  by_cases h4 : x < (2 : ℝ) / 15
  · exact omega_cell_04 x (le_of_not_gt h3) h4
  by_cases h5 : x < (1 : ℝ) / 7
  · exact omega_cell_05 x (le_of_not_gt h4) h5
  by_cases h6 : x < (2 : ℝ) / 13
  · exact omega_cell_06 x (le_of_not_gt h5) h6
  by_cases h7 : x < (1 : ℝ) / 6
  · exact omega_cell_07 x (le_of_not_gt h6) h7
  by_cases h8 : x < (1 : ℝ) / 5
  · exact omega_cell_08 x (le_of_not_gt h7) h8
  by_cases h9 : x < (3 : ℝ) / 14
  · exact omega_cell_09 x (le_of_not_gt h8) h9
  by_cases h10 : x < (3 : ℝ) / 13
  · exact omega_cell_10 x (le_of_not_gt h9) h10
  by_cases h11 : x < (1 : ℝ) / 4
  · exact omega_cell_11 x (le_of_not_gt h10) h11
  by_cases h12 : x < (4 : ℝ) / 15
  · exact omega_cell_12 x (le_of_not_gt h11) h12
  by_cases h13 : x < (2 : ℝ) / 7
  · exact omega_cell_13 x (le_of_not_gt h12) h13
  by_cases h14 : x < (4 : ℝ) / 13
  · exact omega_cell_14 x (le_of_not_gt h13) h14
  by_cases h15 : x < (1 : ℝ) / 3
  · exact omega_cell_15 x (le_of_not_gt h14) h15
  by_cases h16 : x < (5 : ℝ) / 14
  · exact omega_cell_16 x (le_of_not_gt h15) h16
  by_cases h17 : x < (5 : ℝ) / 13
  · exact omega_cell_17 x (le_of_not_gt h16) h17
  by_cases h18 : x < (2 : ℝ) / 5
  · exact omega_cell_18 x (le_of_not_gt h17) h18
  by_cases h19 : x < (5 : ℝ) / 12
  · exact omega_cell_19 x (le_of_not_gt h18) h19
  by_cases h20 : x < (3 : ℝ) / 7
  · exact omega_cell_20 x (le_of_not_gt h19) h20
  by_cases h21 : x < (6 : ℝ) / 13
  · exact omega_cell_21 x (le_of_not_gt h20) h21
  by_cases h22 : x < (7 : ℝ) / 15
  · exact omega_cell_22 x (le_of_not_gt h21) h22
  by_cases h23 : x < (1 : ℝ) / 2
  · exact omega_cell_23 x (le_of_not_gt h22) h23
  by_cases h24 : x < (8 : ℝ) / 15
  · exact omega_cell_24 x (le_of_not_gt h23) h24
  by_cases h25 : x < (7 : ℝ) / 13
  · exact omega_cell_25 x (le_of_not_gt h24) h25
  by_cases h26 : x < (4 : ℝ) / 7
  · exact omega_cell_26 x (le_of_not_gt h25) h26
  by_cases h27 : x < (7 : ℝ) / 12
  · exact omega_cell_27 x (le_of_not_gt h26) h27
  by_cases h28 : x < (3 : ℝ) / 5
  · exact omega_cell_28 x (le_of_not_gt h27) h28
  by_cases h29 : x < (8 : ℝ) / 13
  · exact omega_cell_29 x (le_of_not_gt h28) h29
  by_cases h30 : x < (9 : ℝ) / 14
  · exact omega_cell_30 x (le_of_not_gt h29) h30
  by_cases h31 : x < (2 : ℝ) / 3
  · exact omega_cell_31 x (le_of_not_gt h30) h31
  by_cases h32 : x < (9 : ℝ) / 13
  · exact omega_cell_32 x (le_of_not_gt h31) h32
  by_cases h33 : x < (5 : ℝ) / 7
  · exact omega_cell_33 x (le_of_not_gt h32) h33
  by_cases h34 : x < (11 : ℝ) / 15
  · exact omega_cell_34 x (le_of_not_gt h33) h34
  by_cases h35 : x < (3 : ℝ) / 4
  · exact omega_cell_35 x (le_of_not_gt h34) h35
  by_cases h36 : x < (10 : ℝ) / 13
  · exact omega_cell_36 x (le_of_not_gt h35) h36
  by_cases h37 : x < (11 : ℝ) / 14
  · exact omega_cell_37 x (le_of_not_gt h36) h37
  by_cases h38 : x < (4 : ℝ) / 5
  · exact omega_cell_38 x (le_of_not_gt h37) h38
  by_cases h39 : x < (5 : ℝ) / 6
  · exact omega_cell_39 x (le_of_not_gt h38) h39
  by_cases h40 : x < (11 : ℝ) / 13
  · exact omega_cell_40 x (le_of_not_gt h39) h40
  by_cases h41 : x < (6 : ℝ) / 7
  · exact omega_cell_41 x (le_of_not_gt h40) h41
  by_cases h42 : x < (13 : ℝ) / 15
  · exact omega_cell_42 x (le_of_not_gt h41) h42
  by_cases h43 : x < (11 : ℝ) / 12
  · exact omega_cell_43 x (le_of_not_gt h42) h43
  by_cases h44 : x < (12 : ℝ) / 13
  · exact omega_cell_44 x (le_of_not_gt h43) h44
  by_cases h45 : x < (13 : ℝ) / 14
  · exact omega_cell_45 x (le_of_not_gt h44) h45
  by_cases h46 : x < (14 : ℝ) / 15
  · exact omega_cell_46 x (le_of_not_gt h45) h46
  exact omega_cell_47 x (le_of_not_gt h46) hx1
