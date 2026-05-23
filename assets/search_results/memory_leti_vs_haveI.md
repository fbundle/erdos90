---
name: Typeclass instance identity with structure fields (letI vs haveI)
description: How to avoid haveI creating opaque binders that break def-eq with structure typeclass fields
type: feedback
originSessionId: 15e9ff09-c395-4925-9dd3-d3affcf1131e
---
When a structure has typeclass fields (`[fintypeE : Fintype E]`), and you have a hypothesis `data : Structure`, use **`letI`** not `haveI` to surface the instance.

```lean
-- CORRECT: letI — transparent binder, kernel can unfold to data.fintypeE
letI : Fintype data.E := data.fintypeE

-- WRONG: haveI — opaque binder, NOT def-eq to data.fintypeE
haveI : Fintype data.E := data.fintypeE
```

**Why:** `letI` creates a `let` binder that is definitionally equal to the structure projection. The kernel can unfold it, so `@Fintype.card data.E (letI-binder)` reduces to `@Fintype.card data.E data.fintypeE`. With `haveI`, the binder is opaque and the kernel can't see through it, so `simpa`/`rw`/`linarith` fail with "instance mismatch" errors.

**How to apply:** Whenever a structure field carries a typeclass instance that you need to use, surface it with `letI` (not `haveI`). Then `simpa [data.hcardE]` and similar rewrites work correctly.

**Context:** This was the blocking issue in `cm_norm_one_elements` (§5 of NumberFieldDeep.lean) where `CMClassGroupData` carries `[fintypeE]`, `[fintypeG]`, `[decidableEqE]`, `[decidableEqG]` as typeclass fields. `haveI` broke the connection between `data.h_card_ratio` (using `data.fintypeE`) and the goal (using the `haveI` binder).
