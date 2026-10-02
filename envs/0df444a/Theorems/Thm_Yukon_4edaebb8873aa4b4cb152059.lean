-- Prove2me | Theorems.Thm_Yukon_4edaebb8873aa4b4cb152059
-- name    : Yukon_4edaebb8873aa4b4cb152059
-- status  : Proved
-- author  : @yukon
-- created : 2026-10-02T07:58:04.215427+00:00
-- url     : https://prove2.me/theorems/62cde103-6733-4bdd-bb59-551405331203
-- title:
--   Polynomial.degreeLT_zero
-- statement:
--   `Polynomial.degreeLT R 0 = ⊥`: the only polynomial with degree strictly less than `0`
--   (in `WithBot ℕ`) is the zero polynomial.
--
--   Not `@[simp]` to avoid disrupting existing simp-based proofs that unfold `degreeLT` directly.
-- source:
--   https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/ToMathlib/Polynomial/DegreeLT.lean#L18-L27
--
--   yukon-proof-operation:0a1d9db0-d0a3-4c0c-8bd7-9d6d9d142a9c; Yukon contributor: historical-source-bootstrap
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZGVjNGZhYTk0YTY3YzUzNjRmMWNiMjJjOWY2MjgwYjhhZThmZTgwZDNjZjdlMGZhOGM3Nzk5MzJlYzBlNmFhOCIsImtpbmQiOiJwcm9ibGVtIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOjBhMWQ5ZGIwLWQwYTMtNGMwYy04YmQ3LTlkNmQ5ZDE0MmE5YzsgWXVrb24gY29udHJpYnV0b3I6IGhpc3RvcmljYWwtc291cmNlLWJvb3RzdHJhcCIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uXzRlZGFlYmI4ODczYWE0YjRjYjE1MjA1OSIsInYiOjJ9]

import Definitions.Def_Yukon_56681f993ecf0dddcae4ca01

theorem Yukon_4edaebb8873aa4b4cb152059 : type_of% @Polynomial.degreeLT_zero := by sorry
