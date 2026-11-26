-- Prove2me | Theorems.Thm_section5_window_truncate_error
-- name    : section5_window_truncate_error
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:05:52.742737+00:00
-- url     : https://prove2.me/theorems/171df5d2-2066-53a2-b420-bdce78162fc8
-- title:
--   Strict error bound for a signed integer window
-- statement:
--   Let $P,H$ be positive integers and let $z\in\mathbb Z$ satisfy $-HP\le z<HP$. Let $\operatorname{sres}_H(k)$ be the representative of $k$ modulo $2H$ in $[-H,H)$, and define $W_{P,H}(z)=P\operatorname{sres}_H(\lfloor z/P\rfloor)$. Then
--
--   $$|z-W_{P,H}(z)|<P.$$
--
--   This bounds the discarded low-order part when a signed integer fits inside the represented window.
-- source:
--   Original signed-window arithmetic auxiliary result for Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5. Formalization: Solutions/Section5SignedWindow.lean, lines 33–38.

import Definitions.Def_Section5Verified_Section5SignedWindow
import Mathlib
set_option autoImplicit false

theorem section5_window_truncate_error (P H z : ℤ) (hP : 0 < P) (hH : 0 < H)
    (hlo : -H*P ≤ z) (hhi : z < H*P) :
    |z-section5_window_truncate P H z| < P := by sorry
