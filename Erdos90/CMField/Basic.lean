import Mathlib

open Real Set NumberField Function
open scoped Complex Pointwise nonZeroDivisors

noncomputable section

/-!
# CM field arithmetic infrastructure

This file provides the foundation for working with split prime ideal pairs
in CM fields.  The central definition is `SplitPrimeData`, which packages
a collection of prime ideals 𝔭₁, …, 𝔭ₘ in the ring of integers of a CM
field K together with the guarantee that each is distinct from its complex
conjugate.

## Main definitions

* `SplitPrimeData K m` — m distinct prime ideals, each `≠` its complex conjugate,
  all 2m primes (primes and their conjugates) pairwise distinct.
* `conjIdeal` — complex conjugation on `Ideal (𝓞 K)`, defined directly from
  `ringOfIntegersComplexConj`.
-/

variable (K : Type*) [Field K] [NumberField K] [IsCMField K]

/-- Complex conjugation on `Ideal (𝓞 K)`, directly as an `Ideal` map. -/
noncomputable def conjIdeal : Ideal (𝓞 K) → Ideal (𝓞 K) :=
  Ideal.map ((IsCMField.ringOfIntegersComplexConj K).toRingHom)

@[simp]
lemma conjIdeal_mul (I J : Ideal (𝓞 K)) :
    conjIdeal K (I * J) = (conjIdeal K I) * (conjIdeal K J) := by
  simp [conjIdeal, Ideal.map_mul]

@[simp]
lemma conjIdeal_conjIdeal (I : Ideal (𝓞 K)) :
    conjIdeal K (conjIdeal K I) = I := by
  dsimp [conjIdeal]
  let φ : (𝓞 K) →+* (𝓞 K) := (IsCMField.ringOfIntegersComplexConj K).toRingHom
  have h_alg : ∀ x : 𝓞 K, (IsCMField.ringOfIntegersComplexConj K)
      ((IsCMField.ringOfIntegersComplexConj K) x) = x := by
    intro x
    apply RingOfIntegers.ext_iff.mpr
    calc
      ((IsCMField.ringOfIntegersComplexConj K)
          ((IsCMField.ringOfIntegersComplexConj K) x) : K)
          = IsCMField.complexConj K (((IsCMField.ringOfIntegersComplexConj K) x : K)) := by
        rw [IsCMField.coe_ringOfIntegersComplexConj]
      _ = IsCMField.complexConj K (IsCMField.complexConj K (x : K)) := by
        rw [IsCMField.coe_ringOfIntegersComplexConj]
      _ = (x : K) := by rw [IsCMField.complexConj_apply_apply]
  have h_inv : ∀ x : 𝓞 K, φ (φ x) = x := by
    intro x; dsimp [φ]; exact h_alg x
  have h_comp : φ.comp φ = RingHom.id _ :=
    RingHom.ext h_inv
  calc
    Ideal.map φ (Ideal.map φ I) = (I.map φ).map φ := rfl
    _ = I.map (φ.comp φ) := by rw [Ideal.map_map φ φ]
    _ = I.map (RingHom.id _) := by rw [h_comp]
    _ = I := by rw [Ideal.map_id]


lemma conjIdeal_injective : Function.Injective (conjIdeal K) := by
  intro I J h
  apply_fun conjIdeal K at h
  simpa using h

/-- The conjugate of a nonzero prime ideal is again a nonzero prime ideal. -/
lemma conjIdeal_isPrime {P : Ideal (𝓞 K)} (hP : P.IsPrime) :
    (conjIdeal K P).IsPrime := by
  dsimp [conjIdeal]
  haveI : Ideal.IsPrime P := hP
  exact Ideal.map_isPrime_of_equiv (IsCMField.ringOfIntegersComplexConj K)

lemma conjIdeal_ne_bot {P : Ideal (𝓞 K)} (hP : P ≠ ⊥) :
    conjIdeal K P ≠ ⊥ := by
  intro h_eq
  apply hP
  apply conjIdeal_injective K
  rw [h_eq, conjIdeal, Ideal.map_bot]

section ringEquivOfRingEquiv_coeIdeal

variable (K : Type*) [Field K] [NumberField K]

/-- `ringEquivOfRingEquiv` applied to a coefficient ideal equals
    `(Ideal.map c I : FractionalIdeal ...)`. -/
lemma ringEquivOfRingEquiv_coeIdeal (c : (𝓞 K) ≃+* (𝓞 K)) (I : Ideal (𝓞 K)) :
    FractionalIdeal.ringEquivOfRingEquiv K K c (I : FractionalIdeal (𝓞 K)⁰ K) =
    (Ideal.map (c : (𝓞 K) →+* (𝓞 K)) I : FractionalIdeal (𝓞 K)⁰ K) := by
  ext x
  simp only [FractionalIdeal.ringEquivOfRingEquiv_apply, FractionalIdeal.val_eq_coe,
    FractionalIdeal.coe_coeIdeal, FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, hy⟩
    refine ⟨c z, Ideal.mem_map_of_mem (c : (𝓞 K) →+* (𝓞 K)) hz, ?_⟩
    simpa [IsFractionRing.semilinearEquivOfRingEquiv_apply] using hy
  · rintro ⟨y, hy, rfl⟩
    have h_surj : Function.Surjective (c : (𝓞 K) →+* (𝓞 K)) := by
      intro x; refine ⟨c.symm x, ?_⟩; simp
    rcases (Ideal.mem_map_iff_of_surjective (c : (𝓞 K) →+* (𝓞 K)) h_surj).mp hy with
      ⟨z, hz, rfl⟩
    refine ⟨algebraMap (𝓞 K) K z, ⟨z, hz, rfl⟩, ?_⟩
    simp [IsFractionRing.semilinearEquivOfRingEquiv_apply]

end ringEquivOfRingEquiv_coeIdeal

/-- Data for m split-prime ideal pairs 𝔭ⱼ, c(𝔭ⱼ) in a CM field K.

Each 𝔭ⱼ is a nonzero prime ideal of 𝓞_K, distinct from its complex conjugate,
and all 2m ideals (the primes and their conjugates) are pairwise distinct.
`Q` is the product of the rational primes from which these split-prime pairs
originate (used in the Q² scaling for the α/c(α) membership proof). -/
structure SplitPrimeData (K : Type*) [Field K] [NumberField K] [IsCMField K] (m : ℕ) where
  /-- The m chosen primes; we take one from each conjugate pair. -/
  primes : Fin m → Ideal (𝓞 K)
  /-- Each prime is nonzero (prime in a Dedekind domain). -/
  h_prime : ∀ j, (primes j).IsPrime
  h_ne_bot : ∀ j, primes j ≠ ⊥
  /-- Each prime is split: it is different from its complex conjugate. -/
  h_split : ∀ j, conjIdeal K (primes j) ≠ primes j
  /-- All 2m primes are pairwise distinct.
  Formally: for i, j, and booleans b₁, b₂ (where `true` = the prime itself,
  `false` = its conjugate), equality of the two ideals forces i = j and b₁ = b₂. -/
  h_distinct : ∀ (i j : Fin m) (b₁ b₂ : Bool),
    (if b₁ then primes i else conjIdeal K (primes i)) =
    (if b₂ then primes j else conjIdeal K (primes j)) →
    i = j ∧ b₁ = b₂
  /-- Product of the rational primes q₁,…,qₜ that give rise to these split prime pairs
  (t = m / f where f = nrComplexPlaces).  Used for D₀ = Q² scaling. -/
  Q : ℕ
  h_Q_pos : Q > 0

/-- The conjugate prime `c(𝔭ⱼ)` as an ideal. -/
def SplitPrimeData.conjPrime {m : ℕ} (sp : SplitPrimeData K m) (j : Fin m) : Ideal (𝓞 K) :=
  conjIdeal K (sp.primes j)

/-- Restrict a `SplitPrimeData` of size `m` to the first `n` primes (n ≤ m),
keeping the same `Q`. Used to derive smaller split-prime data from a master
data while preserving the same Q for lattice scaling. -/
def SplitPrimeData.restrict {m : ℕ} (sp : SplitPrimeData K m) (n : ℕ) (hn : n ≤ m) :
    SplitPrimeData K n where
  primes (j : Fin n) := sp.primes ⟨j.1, Nat.lt_of_lt_of_le j.2 hn⟩
  h_prime j := sp.h_prime ⟨j.1, Nat.lt_of_lt_of_le j.2 hn⟩
  h_ne_bot j := sp.h_ne_bot ⟨j.1, Nat.lt_of_lt_of_le j.2 hn⟩
  h_split j := sp.h_split ⟨j.1, Nat.lt_of_lt_of_le j.2 hn⟩
  h_distinct i j b₁ b₂ h_eq := by
    have hd := sp.h_distinct
      ⟨i.1, Nat.lt_of_lt_of_le i.2 hn⟩
      ⟨j.1, Nat.lt_of_lt_of_le j.2 hn⟩ b₁ b₂ h_eq
    rcases hd with ⟨hij, hb⟩
    -- hij : ⟨i.1, _⟩ = ⟨j.1, _⟩ as Fin m, so i.1 = j.1, hence i = j as Fin n
    have hij_val : i.1 = j.1 := by
      have := congrArg Fin.val hij; simpa using this
    refine ⟨Fin.ext hij_val, hb⟩
  Q := sp.Q
  h_Q_pos := sp.h_Q_pos

/-- Convert a `SplitPrimeData` prime to a `HeightOneSpectrum`.
    In a Dedekind domain, nonzero prime ideals are height-1. -/
def SplitPrimeData.toHeightOneSpectrum {m : ℕ} (sp : SplitPrimeData K m)
    (j : Fin m) : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
  ⟨sp.primes j, sp.h_prime j, sp.h_ne_bot j⟩

/-- The conjugate prime as a `HeightOneSpectrum`. -/
def SplitPrimeData.conj_toHeightOneSpectrum {m : ℕ} (sp : SplitPrimeData K m)
    (j : Fin m) : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
  ⟨conjIdeal K (sp.primes j), conjIdeal_isPrime K (sp.h_prime j),
    conjIdeal_ne_bot K (sp.h_ne_bot j)⟩

/-- Conjugate of a `HeightOneSpectrum` under complex conjugation.
    Maps 𝔓 to c(𝔓) = conjIdeal K 𝔓.asIdeal. -/
def conjHeightOneSpectrum (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
  ⟨conjIdeal K v.asIdeal, conjIdeal_isPrime K v.isPrime, conjIdeal_ne_bot K v.ne_bot⟩

@[simp]
lemma conjHeightOneSpectrum_asIdeal (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (conjHeightOneSpectrum K v).asIdeal = conjIdeal K v.asIdeal := rfl

/-- For a nonzero element `a : 𝓞 K`, `count` of `conjIdeal K 𝔓` in the conjugate principal
    ideal `c(a)` equals `count` of `𝔓` in the original principal ideal `(a)`.

    This is the core valuation/count-conjugation lemma.
    Mathematical justification: the ring automorphism `c : 𝓞 K → 𝓞 K` induces a bijection
    on the monoid of nonzero ideals that preserves the factorization into prime ideals
    and maps `𝔓` to `c(𝔓)`. Hence the exponent of `c(𝔓)` in `(c(a))` equals the
    exponent of `𝔓` in `(a)`.

    Reference: Neukirch, Algebraic Number Theory, Proposition I.8.5. -/
lemma count_conj_swap (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (ha : a ≠ 0) :
    FractionalIdeal.count K (conjHeightOneSpectrum K v)
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((IsCMField.ringOfIntegersComplexConj K a : 𝓞 K) : K)) =
    FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K)) := by
  let c : (𝓞 K) ≃+* (𝓞 K) := (IsCMField.ringOfIntegersComplexConj K).toRingEquiv
  let fc : FractionalIdeal (𝓞 K)⁰ K ≃+* FractionalIdeal (𝓞 K)⁰ K :=
    FractionalIdeal.ringEquivOfRingEquiv K K c
  let I : FractionalIdeal (𝓞 K)⁰ K :=
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K)
  have hI_ne_zero : I ≠ 0 := by
    dsimp [I]
    intro h
    rw [FractionalIdeal.spanSingleton_eq_zero_iff] at h
    have ha' : a = (0 : 𝓞 K) := Subtype.coe_injective h
    exact ha ha'
  let Ic : FractionalIdeal (𝓞 K)⁰ K :=
    FractionalIdeal.spanSingleton (𝓞 K)⁰ ((IsCMField.ringOfIntegersComplexConj K a : 𝓞 K) : K)
  have hIc_eq_fcI : Ic = fc I := by
    dsimp [Ic, I, fc]
    rw [FractionalIdeal.ringEquivOfRingEquiv_spanSingleton K K c (a : K)]
    congr 1
    simp [c, IsCMField.coe_ringOfIntegersComplexConj K]
  -- fc maps (v'.asIdeal : FractionalIdeal) to (conj v').asIdeal
  -- The key fact: ringEquivOfRingEquiv K K c applied to a coefficient ideal gives
  -- the conjugate ideal (Ideal.map c v'.asIdeal) as a fractional ideal.
  have h_fc_v (v' : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
      fc (v'.asIdeal : FractionalIdeal (𝓞 K)⁰ K) =
      ((conjHeightOneSpectrum K v').asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
    dsimp [fc, conjHeightOneSpectrum, conjIdeal]
    rw [ringEquivOfRingEquiv_coeIdeal K c v'.asIdeal]
    simp [c]
  have h_fin_I : Set.Finite {v' : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
      FractionalIdeal.count K v' I ≠ 0} :=
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)
  let s : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) := h_fin_I.toFinset
  have hs : ∀ v', v' ∉ s → FractionalIdeal.count K v' I = 0 := by
    intro v' hv'
    have : v' ∉ {v' | FractionalIdeal.count K v' I ≠ 0} := by
      intro h; apply hv'; rw [h_fin_I.mem_toFinset]; exact h
    simpa using this
  have h_mulSupport_subset : mulSupport (fun (v' : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) =>
      ((v'.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (FractionalIdeal.count K v' I : ℤ))) ⊆ (s : Set _) := by
    intro x hx
    by_contra hxs
    have hcount_zero : FractionalIdeal.count K x I = 0 := hs x hxs
    have h_term_one : ((x.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (FractionalIdeal.count K x I : ℤ)) = 1 := by
      simp [hcount_zero]
    exact hx (by dsimp only [mulSupport]; simp [h_term_one])
  have h_factorization_I : I = ∏ v' ∈ s,
      ((v'.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (FractionalIdeal.count K v' I : ℤ)) := by
    have h_finprod := (FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K)
      hI_ne_zero).symm
    rw [finprod_eq_prod_of_mulSupport_subset _ h_mulSupport_subset] at h_finprod
    exact h_finprod
  have h_factorization_Ic : Ic = ∏ v' ∈ s,
      (((conjHeightOneSpectrum K v').asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        (FractionalIdeal.count K v' I : ℤ)) := by
    calc
      Ic = fc I := hIc_eq_fcI
      _ = fc (∏ v' ∈ s, ((v'.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
          (FractionalIdeal.count K v' I : ℤ))) := congrArg fc h_factorization_I
      _ = ∏ v' ∈ s, fc (((v'.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
          (FractionalIdeal.count K v' I : ℤ))) :=
        map_prod fc.toMonoidHom
          (fun v' => ((v'.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (FractionalIdeal.count K v' I : ℤ))) s
      _ = ∏ v' ∈ s, (fc (v'.asIdeal : FractionalIdeal (𝓞 K)⁰ K)) ^
          (FractionalIdeal.count K v' I : ℤ) := by
        refine Finset.prod_congr rfl (fun v' _hv' => ?_)
        exact map_zpow₀ fc ((v'.asIdeal : FractionalIdeal (𝓞 K)⁰ K)) (FractionalIdeal.count K v' I : ℤ)
      _ = ∏ v' ∈ s, (((conjHeightOneSpectrum K v').asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
          (FractionalIdeal.count K v' I : ℤ)) := by
        simp [h_fc_v]
  have h_count_sum : FractionalIdeal.count K (conjHeightOneSpectrum K v)
      (∏ v' ∈ s, (((conjHeightOneSpectrum K v').asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        (FractionalIdeal.count K v' I : ℤ))) =
      FractionalIdeal.count K v I := by
    rw [FractionalIdeal.count_prod K (conjHeightOneSpectrum K v) s
      (fun v' => (((conjHeightOneSpectrum K v').asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        (FractionalIdeal.count K v' I : ℤ))) (by
          intro v' _hv'
          exact zpow_ne_zero (FractionalIdeal.count K v' I : ℤ)
            (FractionalIdeal.coeIdeal_ne_zero.mpr (conjHeightOneSpectrum K v').ne_bot))]
    simp_rw [FractionalIdeal.count_zpow]
    classical
    have h_count_conj : ∀ (v' : IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
        FractionalIdeal.count K (conjHeightOneSpectrum K v)
          ((conjHeightOneSpectrum K v').asIdeal : FractionalIdeal (𝓞 K)⁰ K) =
        if v' = v then (1 : ℤ) else 0 := by
      intro v'
      by_cases hv' : v' = v
      · rw [← hv']
        have h := FractionalIdeal.count_self (R := 𝓞 K) (K := K) (v := conjHeightOneSpectrum K v')
        simpa using h
      · have hne : conjHeightOneSpectrum K v' ≠ conjHeightOneSpectrum K v := by
          intro h
          apply hv'
          apply IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
          apply conjIdeal_injective K
          simpa [conjHeightOneSpectrum] using congrArg (fun x => x.asIdeal) h
        rw [FractionalIdeal.count_maximal_coprime K (conjHeightOneSpectrum K v) hne]
        simp [hv']
    simp_rw [h_count_conj]
    by_cases hv : v ∈ s
    · calc
        (∑ v' ∈ s, ((FractionalIdeal.count K v' I : ℤ) * (if v' = v then (1 : ℤ) else 0 : ℤ)))
            = ((FractionalIdeal.count K v I : ℤ) * (1 : ℤ)) := by
          refine (Finset.sum_eq_single v (fun v'' hv'' hvne => ?_) (fun hv_not => ?_)).trans ?_
          · simp [hvne]
          · exact absurd hv hv_not
          · simp
        _ = FractionalIdeal.count K v I := by simp
    · have hzero : FractionalIdeal.count K v I = 0 := hs v hv
      calc
        (∑ v' ∈ s, ((FractionalIdeal.count K v' I : ℤ) * (if v' = v then (1 : ℤ) else 0 : ℤ))) = 0 := by
          apply Finset.sum_eq_zero; intro v' hv'
          have hne : v' ≠ v := by
            intro h; subst h; exact hv hv'
          simp [hne]
        _ = FractionalIdeal.count K v I := by rw [hzero]
  calc
    FractionalIdeal.count K (conjHeightOneSpectrum K v) Ic
        = FractionalIdeal.count K (conjHeightOneSpectrum K v)
            (∏ v' ∈ s, (((conjHeightOneSpectrum K v').asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
              (FractionalIdeal.count K v' I : ℤ))) := by rw [h_factorization_Ic]
    _ = FractionalIdeal.count K v I := h_count_sum
    _ = FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K)) := rfl

/-- General version: `count` is invariant under the complex conjugation ring isomorphism
    applied to both the prime and the ideal.

    For any nonzero fractional ideal `I` and HeightOneSpectrum `v`,
    `count` at the conjugate prime `c(v)` of the conjugate ideal `c(I)`
    equals `count` at `v` of `I`. -/
lemma count_conj_swap' (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI_ne_zero : I ≠ 0) :
    FractionalIdeal.count K (conjHeightOneSpectrum K v)
      (FractionalIdeal.ringEquivOfRingEquiv K K
        ((IsCMField.ringOfIntegersComplexConj K).toRingEquiv) I) =
    FractionalIdeal.count K v I := by
  let c : (𝓞 K) ≃+* (𝓞 K) := (IsCMField.ringOfIntegersComplexConj K).toRingEquiv
  let fc : FractionalIdeal (𝓞 K)⁰ K ≃+* FractionalIdeal (𝓞 K)⁰ K :=
    FractionalIdeal.ringEquivOfRingEquiv K K c
  have h_fc_v (v' : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
      fc (v'.asIdeal : FractionalIdeal (𝓞 K)⁰ K) =
      ((conjHeightOneSpectrum K v').asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
    dsimp [fc, conjHeightOneSpectrum, conjIdeal]
    rw [ringEquivOfRingEquiv_coeIdeal K c v'.asIdeal]
    simp [c]
  have h_fin_I : Set.Finite {v' : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
      FractionalIdeal.count K v' I ≠ 0} :=
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)
  let s : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) := h_fin_I.toFinset
  have hs : ∀ v', v' ∉ s → FractionalIdeal.count K v' I = 0 := by
    intro v' hv'
    have : v' ∉ {v' | FractionalIdeal.count K v' I ≠ 0} := by
      intro h; apply hv'; rw [h_fin_I.mem_toFinset]; exact h
    simpa using this
  have h_mulSupport_subset : mulSupport (fun (v' : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) =>
      ((v'.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (FractionalIdeal.count K v' I : ℤ))) ⊆ (s : Set _) := by
    intro x hx
    by_contra hxs
    have hcount_zero : FractionalIdeal.count K x I = 0 := hs x hxs
    have h_term_one : ((x.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (FractionalIdeal.count K x I : ℤ)) = 1 := by
      simp [hcount_zero]
    exact hx (by dsimp only [mulSupport]; simp [h_term_one])
  have h_factorization_I : I = ∏ v' ∈ s,
      ((v'.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (FractionalIdeal.count K v' I : ℤ)) := by
    have h_finprod := (FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K)
      hI_ne_zero).symm
    rw [finprod_eq_prod_of_mulSupport_subset _ h_mulSupport_subset] at h_finprod
    exact h_finprod
  have h_factorization_fcI : fc I = ∏ v' ∈ s,
      (((conjHeightOneSpectrum K v').asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        (FractionalIdeal.count K v' I : ℤ)) := by
    calc
      fc I = fc (∏ v' ∈ s, ((v'.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
          (FractionalIdeal.count K v' I : ℤ))) := congrArg fc h_factorization_I
      _ = ∏ v' ∈ s, fc (((v'.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
          (FractionalIdeal.count K v' I : ℤ))) :=
        map_prod fc.toMonoidHom
          (fun v' => ((v'.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (FractionalIdeal.count K v' I : ℤ))) s
      _ = ∏ v' ∈ s, (fc (v'.asIdeal : FractionalIdeal (𝓞 K)⁰ K)) ^
          (FractionalIdeal.count K v' I : ℤ) := by
        refine Finset.prod_congr rfl (fun v' _hv' => ?_)
        exact map_zpow₀ fc ((v'.asIdeal : FractionalIdeal (𝓞 K)⁰ K)) (FractionalIdeal.count K v' I : ℤ)
      _ = ∏ v' ∈ s, (((conjHeightOneSpectrum K v').asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
          (FractionalIdeal.count K v' I : ℤ)) := by
        simp [h_fc_v]
  have h_count_sum : FractionalIdeal.count K (conjHeightOneSpectrum K v)
      (∏ v' ∈ s, (((conjHeightOneSpectrum K v').asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        (FractionalIdeal.count K v' I : ℤ))) =
      FractionalIdeal.count K v I := by
    rw [FractionalIdeal.count_prod K (conjHeightOneSpectrum K v) s
      (fun v' => (((conjHeightOneSpectrum K v').asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        (FractionalIdeal.count K v' I : ℤ))) (by
          intro v' _hv'
          exact zpow_ne_zero (FractionalIdeal.count K v' I : ℤ)
            (FractionalIdeal.coeIdeal_ne_zero.mpr (conjHeightOneSpectrum K v').ne_bot))]
    simp_rw [FractionalIdeal.count_zpow]
    classical
    have h_count_conj : ∀ (v' : IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
        FractionalIdeal.count K (conjHeightOneSpectrum K v)
          ((conjHeightOneSpectrum K v').asIdeal : FractionalIdeal (𝓞 K)⁰ K) =
        if v' = v then (1 : ℤ) else 0 := by
      intro v'
      by_cases hv' : v' = v
      · rw [← hv']
        have h := FractionalIdeal.count_self (R := 𝓞 K) (K := K) (v := conjHeightOneSpectrum K v')
        simpa using h
      · have hne : conjHeightOneSpectrum K v' ≠ conjHeightOneSpectrum K v := by
          intro h
          apply hv'
          apply IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
          apply conjIdeal_injective K
          simpa [conjHeightOneSpectrum] using congrArg (fun x => x.asIdeal) h
        rw [FractionalIdeal.count_maximal_coprime K (conjHeightOneSpectrum K v) hne]
        simp [hv']
    simp_rw [h_count_conj]
    by_cases hv : v ∈ s
    · calc
        (∑ v' ∈ s, ((FractionalIdeal.count K v' I : ℤ) * (if v' = v then (1 : ℤ) else 0 : ℤ)))
            = ((FractionalIdeal.count K v I : ℤ) * (1 : ℤ)) := by
          refine (Finset.sum_eq_single v (fun v'' hv'' hvne => ?_) (fun hv_not => ?_)).trans ?_
          · simp [hvne]
          · exact absurd hv hv_not
          · simp
        _ = FractionalIdeal.count K v I := by simp
    · have hzero : FractionalIdeal.count K v I = 0 := hs v hv
      calc
        (∑ v' ∈ s, ((FractionalIdeal.count K v' I : ℤ) * (if v' = v then (1 : ℤ) else 0 : ℤ))) = 0 := by
          apply Finset.sum_eq_zero; intro v' hv'
          have hne : v' ≠ v := by
            intro h; subst h; exact hv hv'
          simp [hne]
        _ = FractionalIdeal.count K v I := by rw [hzero]
  calc
    FractionalIdeal.count K (conjHeightOneSpectrum K v)
        (FractionalIdeal.ringEquivOfRingEquiv K K c I) =
      FractionalIdeal.count K (conjHeightOneSpectrum K v)
        (∏ v' ∈ s, (((conjHeightOneSpectrum K v').asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
          (FractionalIdeal.count K v' I : ℤ))) := by rw [h_factorization_fcI]
    _ = FractionalIdeal.count K v I := h_count_sum

/-- The ideal product J(ε) = ∏_j (if ε_j then 𝔓_j else c(𝔓_j)), as a fractional ideal.
    Defined directly as a FractionalIdeal product for convenient use with `count_prod`. -/
def J_ideal {m : ℕ} (sp : SplitPrimeData K m) (ε : Fin m → Bool) :
    FractionalIdeal (𝓞 K)⁰ K :=
  ∏ j ∈ Finset.univ, (if ε j then (sp.primes j : FractionalIdeal (𝓞 K)⁰ K)
    else (conjIdeal K (sp.primes j) : FractionalIdeal (𝓞 K)⁰ K))

lemma J_ideal_ne_zero {m : ℕ} (sp : SplitPrimeData K m) (ε : Fin m → Bool) :
    J_ideal K sp ε ≠ 0 := by
  dsimp [J_ideal]
  refine Finset.prod_ne_zero_iff.mpr (fun j _ => ?_)
  split
  · exact FractionalIdeal.coeIdeal_ne_zero.mpr (sp.h_ne_bot j)
  · exact FractionalIdeal.coeIdeal_ne_zero.mpr (conjIdeal_ne_bot K (sp.h_ne_bot j))

/-- Helper: `toHeightOneSpectrum i = toHeightOneSpectrum j` implies `i = j`. -/
lemma toHeightOneSpectrum_inj {m : ℕ} (sp : SplitPrimeData K m) {i j : Fin m}
    (h : sp.toHeightOneSpectrum (j := i) = sp.toHeightOneSpectrum (j := j)) : i = j := by
  have h_ideal : sp.primes i = sp.primes j := by
    simpa [SplitPrimeData.toHeightOneSpectrum] using congrArg (fun v => v.asIdeal) h
  have := sp.h_distinct i j true true (by simpa using h_ideal)
  exact this.1

lemma conj_toHeightOneSpectrum_ne_toHeightOneSpectrum {m : ℕ} (sp : SplitPrimeData K m) (i j : Fin m) :
    sp.conj_toHeightOneSpectrum (j := i) ≠ sp.toHeightOneSpectrum (j := j) := by
  intro h
  have h_ideal : conjIdeal K (sp.primes i) = sp.primes j := by
    simpa [SplitPrimeData.conj_toHeightOneSpectrum, SplitPrimeData.toHeightOneSpectrum]
      using congrArg (fun v => v.asIdeal) h
  have hc := sp.h_distinct i j false true (by simpa using h_ideal)
  exact Bool.noConfusion hc.2

/-- For the ideal product `J ε`, the `count` at prime `sp.toHeightOneSpectrum s`
    is 1 if `ε s = true` and 0 otherwise. -/
lemma count_J_eq {m : ℕ} (sp : SplitPrimeData K m) (ε : Fin m → Bool) (s : Fin m) :
    FractionalIdeal.count K (sp.toHeightOneSpectrum (j := s)) (J_ideal K sp ε) =
      if ε s then 1 else 0 := by
  classical
  let v := sp.toHeightOneSpectrum (j := s)
  have hS : ∀ (j : Fin m), (if ε j then (sp.primes j : FractionalIdeal (𝓞 K)⁰ K)
      else (conjIdeal K (sp.primes j) : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0 := by
    intro j; split
    · exact FractionalIdeal.coeIdeal_ne_zero.mpr (sp.h_ne_bot j)
    · exact FractionalIdeal.coeIdeal_ne_zero.mpr (conjIdeal_ne_bot K (sp.h_ne_bot j))
  dsimp [J_ideal]
  have hcount := FractionalIdeal.count_prod K v (Finset.univ : Finset (Fin m))
    (fun j => if ε j then (sp.primes j : FractionalIdeal (𝓞 K)⁰ K)
              else (conjIdeal K (sp.primes j) : FractionalIdeal (𝓞 K)⁰ K))
    (fun j hj => hS j)
  rw [hcount]
  have hsum : (∑ j : Fin m,
      FractionalIdeal.count K v (if ε j then (sp.primes j : FractionalIdeal (𝓞 K)⁰ K)
        else (conjIdeal K (sp.primes j) : FractionalIdeal (𝓞 K)⁰ K))) =
      (∑ j : Fin m, if j = s ∧ ε j then (1 : ℤ) else 0) := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    cases hεj : ε j
    · -- ε j = false
      simp
      have h_eq : (conjIdeal K (sp.primes j) : FractionalIdeal (𝓞 K)⁰ K) =
          ((sp.conj_toHeightOneSpectrum (j := j)).asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
        simp [SplitPrimeData.conj_toHeightOneSpectrum]
      rw [h_eq]
      have h_ne : sp.conj_toHeightOneSpectrum (j := j) ≠ v :=
        conj_toHeightOneSpectrum_ne_toHeightOneSpectrum (K := K) sp j s
      exact FractionalIdeal.count_maximal_coprime (R := 𝓞 K) (K := K) (v := v)
        (w := sp.conj_toHeightOneSpectrum (j := j)) h_ne
    · -- ε j = true
      simp
      have h_eq : (sp.primes j : FractionalIdeal (𝓞 K)⁰ K) =
          ((sp.toHeightOneSpectrum (j := j)).asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
        simp [SplitPrimeData.toHeightOneSpectrum]
      rw [h_eq]
      rw [FractionalIdeal.count_maximal (R := 𝓞 K) (K := K) (v := v)
        (w := sp.toHeightOneSpectrum (j := j))]
      by_cases hjs : j = s
      · subst hjs; simp [v]
      · have hne : sp.toHeightOneSpectrum (j := j) ≠ v := by
          intro heq; apply hjs; exact toHeightOneSpectrum_inj (K := K) sp heq
        simp [hne, hjs, v]
  rw [hsum]
  rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin m))
    (fun j => if j = s ∧ ε j then (1 : ℤ) else 0) (Finset.mem_univ s)]
  have h_erase : (∑ j ∈ (Finset.univ : Finset (Fin m)).erase s,
      if j = s ∧ ε j then (1 : ℤ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjne : j ≠ s := (Finset.mem_erase.mp hj).1
    simp [hjne]
  rw [h_erase]
  cases ε s <;> simp

/-- For the ideal product `J ε`, the `count` at the conjugate prime
    `conj_toHeightOneSpectrum s` is 1 if `ε s = false` and 0 otherwise. -/
lemma count_J_conj_eq {m : ℕ} (sp : SplitPrimeData K m) (ε : Fin m → Bool) (s : Fin m) :
    FractionalIdeal.count K (sp.conj_toHeightOneSpectrum (j := s)) (J_ideal K sp ε) =
      if ε s then 0 else 1 := by
  classical
  let v := sp.conj_toHeightOneSpectrum (j := s)
  have hS : ∀ (j : Fin m), (if ε j then (sp.primes j : FractionalIdeal (𝓞 K)⁰ K)
      else (conjIdeal K (sp.primes j) : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0 := by
    intro j; split
    · exact FractionalIdeal.coeIdeal_ne_zero.mpr (sp.h_ne_bot j)
    · exact FractionalIdeal.coeIdeal_ne_zero.mpr (conjIdeal_ne_bot K (sp.h_ne_bot j))
  dsimp [J_ideal]
  have hcount := FractionalIdeal.count_prod K v (Finset.univ : Finset (Fin m))
    (fun j => if ε j then (sp.primes j : FractionalIdeal (𝓞 K)⁰ K)
              else (conjIdeal K (sp.primes j) : FractionalIdeal (𝓞 K)⁰ K))
    (fun j hj => hS j)
  rw [hcount]
  have hsum : (∑ j : Fin m,
      FractionalIdeal.count K v (if ε j then (sp.primes j : FractionalIdeal (𝓞 K)⁰ K)
        else (conjIdeal K (sp.primes j) : FractionalIdeal (𝓞 K)⁰ K))) =
      (∑ j : Fin m, if j = s ∧ ¬ ε j then (1 : ℤ) else 0) := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    cases hεj : ε j
    · -- ε j = false
      simp
      have h_eq : (conjIdeal K (sp.primes j) : FractionalIdeal (𝓞 K)⁰ K) =
          ((sp.conj_toHeightOneSpectrum (j := j)).asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
        simp [SplitPrimeData.conj_toHeightOneSpectrum]
      rw [h_eq]
      rw [FractionalIdeal.count_maximal (R := 𝓞 K) (K := K) (v := v)
        (w := sp.conj_toHeightOneSpectrum (j := j))]
      by_cases hjs : j = s
      · subst hjs; simp [v]
      · have hne : sp.conj_toHeightOneSpectrum (j := j) ≠ v := by
          intro heq; apply hjs
          have h_ideal : conjIdeal K (sp.primes j) = conjIdeal K (sp.primes s) := by
            simpa [SplitPrimeData.conj_toHeightOneSpectrum, v]
              using congrArg (fun v => v.asIdeal) heq
          have h_primes : sp.primes j = sp.primes s := conjIdeal_injective K h_ideal
          have hc := sp.h_distinct j s true true (by simpa using h_primes)
          exact hc.1
        simp [hne, hjs, v]
    · -- ε j = true
      simp
      have h_ne : sp.toHeightOneSpectrum (j := j) ≠ v := by
        intro heq
        have h_ideal : sp.primes j = conjIdeal K (sp.primes s) := by
          simpa [SplitPrimeData.toHeightOneSpectrum, SplitPrimeData.conj_toHeightOneSpectrum, v]
            using congrArg (fun v => v.asIdeal) heq
        have hc := sp.h_distinct j s true false (by simpa using h_ideal)
        exact Bool.noConfusion hc.2
      have h_eq : (sp.primes j : FractionalIdeal (𝓞 K)⁰ K) =
          ((sp.toHeightOneSpectrum (j := j)).asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
        simp [SplitPrimeData.toHeightOneSpectrum]
      rw [h_eq]
      exact FractionalIdeal.count_maximal_coprime (R := 𝓞 K) (K := K) (v := v)
        (w := sp.toHeightOneSpectrum (j := j)) h_ne
  rw [hsum]
  rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin m))
    (fun j => if j = s ∧ ¬ ε j then (1 : ℤ) else 0) (Finset.mem_univ s)]
  have h_erase : (∑ j ∈ (Finset.univ : Finset (Fin m)).erase s,
      if j = s ∧ ¬ ε j then (1 : ℤ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjne : j ≠ s := (Finset.mem_erase.mp hj).1
    simp [hjne]
  rw [h_erase]
  cases ε s <;> simp

/-- For an element γ ∈ K^× fixed by complex conjugation, the `count` at a prime 𝔓
    equals the `count` at the conjugate prime c(𝔓).
    Follows from `count_conj_swap'` and the fact that `c(γ) = γ` implies the
    principal fractional ideal `(γ)` is fixed by the ring isomorphism. -/
lemma count_eq_count_conj_of_fixed {γ : K} (hγ : γ ≠ 0) (h_fixed : IsCMField.complexConj K γ = γ)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ γ) =
    FractionalIdeal.count K (conjHeightOneSpectrum K v)
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ γ) := by
  let c : (𝓞 K) ≃+* (𝓞 K) := (IsCMField.ringOfIntegersComplexConj K).toRingEquiv
  let I : FractionalIdeal (𝓞 K)⁰ K := FractionalIdeal.spanSingleton (𝓞 K)⁰ γ
  have hI_ne_zero : I ≠ 0 := by
    dsimp [I]
    intro h
    rw [FractionalIdeal.spanSingleton_eq_zero_iff] at h
    exact hγ h
  have h_c_field_eq : (IsFractionRing.ringEquivOfRingEquiv (A := 𝓞 K) (K := K) (B := 𝓞 K) (L := K) c : K →+* K) =
      (IsCMField.complexConj K : K →+* K) := by
    apply IsFractionRing.ringHom_ext (A := 𝓞 K) (K := K) (L := K)
    intro a
    simp [c, IsCMField.coe_ringOfIntegersComplexConj K]
  have h_cγ : IsFractionRing.ringEquivOfRingEquiv (A := 𝓞 K) (K := K) (B := 𝓞 K) (L := K) c γ = γ := by
    calc
      IsFractionRing.ringEquivOfRingEquiv (A := 𝓞 K) (K := K) (B := 𝓞 K) (L := K) c γ
          = ((IsFractionRing.ringEquivOfRingEquiv (A := 𝓞 K) (K := K) (B := 𝓞 K) (L := K) c : K →+* K)) γ := rfl
      _ = (IsCMField.complexConj K : K →+* K) γ := by rw [h_c_field_eq]
      _ = γ := h_fixed
  have h_conj_I : FractionalIdeal.ringEquivOfRingEquiv K K c I = I := by
    dsimp [I]
    rw [FractionalIdeal.ringEquivOfRingEquiv_spanSingleton K K c γ]
    simp [h_cγ]
  have h_eq := count_conj_swap' K v I hI_ne_zero
  rw [h_conj_I] at h_eq
  exact h_eq.symm

end
