-- Prove2me | Theorems.Thm_mme_released_positive_integer_frame
-- name    : mme_released_positive_integer_frame
-- status  : Proved
-- author  : @BrunoDCDO
-- created : 2026-09-24T02:25:38.932386+00:00
-- url     : https://prove2.me/theorems/8aa8d8f3-b4a4-4716-9fdf-b63581bd2434
-- title:
--   The compact released regions admit positive integer frames
-- statement:
--   For every released inner region $\rho\in\{0,\ldots,5\}$ and every natural-number scale $k>0$, there exists a positive integer frame for the 88 compact labels of that region.
--
--   The frame uses the exact scaled data $k n_3$, $k m_3$, and $k\mu_3$. It contains a reference address with the prescribed split histogram, enumerations of all parent and child positions, exact marginal masses, grade support, boundary symmetry, minimum parent size $kD^2$, and split-count divisibility by $kD^2$, where $D=10^{12}$. Its child enumeration preserves parent grading and identifies the compact parent-typical band with the canonical common source for every positive tolerance.
--
--   Neither a repair scale nor a tolerance is chosen in this existence statement. The frame's transparent constructor builds an `IntegerStep` once those parameters satisfy its explicit scalar size test. No hypothesis about output copies, entropy rates, or the final recursive budget is assumed.
-- source:
--   Finite-data assembly interface for the published RecStage tables (p2m:theorem/60610bd3-0675-4be4-a731-ca71c173a5bc, marwahaha), common profiles and position frame (p2m:theorem/3d489536-019f-46c1-b6c3-52ee24f948d0 and p2m:theorem/8bcbc67f-e01e-4bd0-ad82-deb2f4e5b904, Robertboy18), and released exact seed (p2m:theorem/cb80ec03-0b0a-4b6c-a75e-ca788b94d914, raresbuhai). Underlying regional construction: Alman, Duan, Vassilevska Williams, Xu, Xu and Zhou, More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/pdf/2404.16349v2, Section 6.1 and Claim 6.5, printed page 32. This interface is not stated verbatim in the paper; the present theorem proves its existence using the common integer constraints p2m:theorem/ee09ae5d-6c3a-445f-975d-f607f4531dd7, the six positive-profile correspondences, and positive-position transport p2m:theorem/3e00b541-91ad-4872-8a46-f4ae86ba0b51.

import Definitions.Def_mme_released_positive_integer_frame_data
set_option autoImplicit false

theorem mme_released_positive_integer_frame (region : Fin 6) (k : ℕ) (hk : 0 < k) :
    Nonempty (MME.ReleasedPositiveInteger.Frame region k) := by sorry
