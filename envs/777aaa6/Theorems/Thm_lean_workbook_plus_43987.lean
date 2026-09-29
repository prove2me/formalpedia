-- Prove2me | Theorems.Thm_lean_workbook_plus_43987
-- name    : lean_workbook_plus_43987
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/10d0a482-f165-48d4-bfb6-e4a911b9f8a3
-- statement:
--   Given $n\in\mathbb Z_+.$ For $\forall 1\leq k\leq n,z_k,\omega _k\in\mathbb C.$ For $\forall \epsilon_1,\epsilon_2,\cdots,\epsilon_n\in\{-1,1\},$ prove that:\n\n $$\left|\sum\limits_{k=1}^n\epsilon_kz_k\right|^2\leqslant\left|\sum\limits_{k=1}^n\epsilon_k\omega _k\right|^2.$$ \n\nimplies \n\n $$\sum\limits_{k=1}^n|z_k|^2\leqslant\sum\limits_{k=1}^n|\omega _k|^2.$$\n\nFirst we use induction to prove that for $\forall n\in\mathbb Z_+,$\n\n $$\sum\limits_{\epsilon_1\in\{-1,1\}}\sum\limits_{\epsilon_2\in\{-1,1\}}\cdots\sum\limits_{\epsilon_n\in\{-1,1\}}\left|\sum\limits_{k=1}^n\epsilon_kz_k\right|^2=2^{n}\sum\limits_{k=1}^n|z_k|^2,$$ $$\sum\limits_{\epsilon_1\in\{-1,1\}}\sum\limits_{\epsilon_2\in\{-1,1\}}\cdots\sum\limits_{\epsilon_n\in\{-1,1\}}\left|\sum\limits_{k=1}^n\epsilon_k\omega _k\right|^2=2^{n}\sum\limits_{k=1}^n|\omega _k|^2.$$ When $n=1,$ it is obvious $.$ When $n=2,$ we have $|z_1+z_2|^2+|z_1-z_2|^2=2|z_1|^2+2|z_2|^2,$ so it is true as well $.$ \n\nNow let $n\geq 3,$ and we have \n\n $$\sum\limits_{\epsilon_1\in\{-1,1\}}\sum\limits_{\epsilon_2\in\{-1,1\}}\cdots\sum\limits_{\epsilon_{n-1}\in\{-1,1\}}\left|\sum\limits_{k=1}^{n-1}\epsilon_kz_k\right|^2=2^{n-1}\sum\limits_{k=1}^n|z_k|^2.$$ Then we can get \n\n $$\begin{aligned}\sum\limits_{\epsilon_1\in\{-1,1\}}\sum\limits_{\epsilon_2\in\{-1,1\}}\cdots\sum\limits_{\epsilon_n\in\{-1,1\}}\left|\sum\limits_{k=1}^n\epsilon_kz_k\right|^2&=\sum\limits_{\epsilon_1\in\{-1,1\}}\sum\limits_{\epsilon_2\in\{-1,1\}}\cdots\sum\limits_{\epsilon_{n-1}\in\{-1,1\}}\left(\left|\sum\limits_{k=1}^{n-1}\epsilon_kz_k+z_n\right|^2+\left|\sum\limits_{k=1}^{n-1}\epsilon_kz_k-z_n\right|^2\right)\\&=2\sum\limits_{\epsilon_1\in\{-1,1\}}\sum\limits_{\epsilon_2\in\{-1,1\}}\cdots\sum\limits_{\epsilon_{n-1}\in\{-1,1\}}\left(\left|\sum\limits_{k=1}^{n-1}\epsilon_kz_k\right|^2+|z_n|^2\right)\\&=2\sum\limits_{\epsilon_1\in\{-1,1\}}\sum\limits_{\epsilon_2\in\{-1,1\}}\cdots\sum\limits_{\epsilon_{n-1}\in\{-1,1\}}\left|\sum\limits_{k=1}^{n-1}\epsilon_kz_k\right|^2+2^n|z_n|^2\\&=2^{n}\sum\limits_{k=1}^{n-1}|z_k|^2+2^n|z_n|^2\\&=2^{n}\sum\limits_{k=1}^n|z_k|^2.\end{aligned}$$ Using the same method we have \n\n $$\sum\limits_{\epsilon_1\in\{-1,1\}}\sum\limits_{\epsilon_2\in\{-1,1\}}\cdots\sum\limits_{\epsilon_n\in\{-1,1\}}\left|\sum\limits_{k=1}^n\epsilon_k\omega _k\right|^2=2^{n}\sum\limits_{k=1}^n|\omega _k|^2.$$ Therefore \n\n $$\sum\limits_{k=1}^n|z_k|^2=\dfrac 1{2^n}\sum\limits_{\epsilon_1\in\{-1,1\}}\sum\limits_{\epsilon_2\in\{-1,1\}}\cdots\sum\limits_{\epsilon_n\in\{-1,1\}}\left|\sum\limits_{k=1}^n\epsilon_kz_k\right|^2\leqslant\dfrac 1{2^n}\sum\limits_{\epsilon_1\in\{-1,1\}}\sum\limits_{\epsilon_2\in\{-1,1\}}\cdots\sum\limits_{\epsilon_n\in\{-1,1\}}\left|\sum\limits_{k=1}^n\epsilon_k\omega_k\right|^2=\sum\limits_{k=1}^n|\omega _k|^2.\blacksquare$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43987  (n : ℕ)
  (z omega : Fin n → ℂ)
  (h₀ : ∀ k, ‖z k‖ = ‖omega k‖)
  (h₁ : ∀ k, 0 < ‖z k‖) :
  ∑ k, ‖z k‖^2 ≤ ∑ k, ‖omega k‖^2   :=  by sorry
