import Verification.defs_timeHT

open HofT

universe T

/-
Axioms to ensure the successor and predecessor relation is a total, linear order
-/
axiom transitivity {κ : Type T} :
  ∀ (n : ℕ)
  (τ : Set (timeline κ n × timeline κ n))
  (A B C : timeline κ n),
  (B ∈ succs A τ ∧ C ∈ succs B τ)
  → C ∈ succs A τ

axiom irreflexivity {κ : Type T} :
  ∀ (n : ℕ)
  (τ : Set (timeline κ n × timeline κ n))
  (A : timeline κ n),
  ¬(A ∈ succs A τ)

axiom totality {κ : Type T} :
  ∀ (n : ℕ)
  (τ : Set (timeline κ n × timeline κ n))
  (A B : timeline κ n),
  (A ∈ ffld τ ∧ B ∈ ffld τ ∧ valid_timeline τ)
  → (A ∈ succs B τ ∨ A = B ∨ B ∈ succs A τ)

axiom projection_ordering {κ : Type T} :
  ∀ (n k : ℕ)
  (Ξ : timeline κ (n + k + 2))
  (τ ρ : timeline κ (n + k + 1)),
  ρ ∈ succs τ Ξ → ∀ (A B : timeline κ (n)), (B ∈ fld n k ρ ∧ A ∈ fld n k τ)
  → B ∈ succs A (proj n k Ξ)

theorem fundamental {κ : Type T} :
  ∀ (n : ℕ)
  (τ : Set (timeline κ n × timeline κ n)),
  ∃ (t : timeline κ (n + 1)),
  t = τ := by
  intro n T
  exact ⟨T, rfl⟩

theorem fundnonbranching {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  nonbranching τ → ∀ (p : timeline κ n × timeline κ n),
  p ∈ τ → ∀ q ∈ τ, q.2 ≠ p.2 ↔ q.1 ≠ p.1 := by
  intro T nbT p pinT q qinT
  unfold nonbranching at nbT
  replace nbT := (nbT q qinT p pinT)
  exact (not_iff_not.mpr nbT).symm

theorem validnonbranching {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  valid_timeline τ → nonbranching τ := by
  intro T vT
  unfold valid_timeline at vT
  rcases vT with ⟨first, last⟩
  exact first

theorem validnonempty {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  valid_timeline τ → τ.Nonempty := by
  intro T ⟨A, B, C, D⟩
  exact D

/-
!SING# : Theorems regarding single timelines
SING0 : The cardinality of a timeline that is single is exact 1
SING1 : Any proper subset ("proper subset" meaning, for example, A ⊆ B ∧ A ≠ B)
        of a single timeline is equal to the empty set
-/
theorem SING0 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  single τ → Set.ncard τ = 1 := by
    intro T singT
    unfold single at singT
    rcases singT with ⟨nempt, p, hp⟩
    have sthm1 : T = {p} := by
      rw [Set.ext_iff]
      intro x
      have ssthm1 := hp x
      simp only [Set.mem_singleton_iff]
      exact ssthm1
    simp only [Set.ncard_eq_one]
    exact ⟨p, sthm1⟩

theorem SING1 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  single τ → ∀ X ⊆ τ, Set.ncard X < Set.ncard τ
  → X = ∅ := by
  intro T singT X subX lessX
  unfold single at singT
  have sthm1 := SING0 T singT
  rw [sthm1] at lessX
  have zeroX : X.ncard = 0 := by
    exact Nat.lt_one_iff.mp lessX
  rw [Set.empty_def]
  rw [Set.ext_iff]
  intro x
  rw [Set.subset_def] at subX
  have sthm2 : T.ncard ≠ 0 := by
    omega
  have sthm3 : T.Finite := by
    exact Set.finite_of_ncard_ne_zero sthm2
  have sthm4 : X.Finite := sthm3.subset subX
  constructor
  · intro h1
    simp only [Set.setOf_false, Set.mem_empty_iff_false]
    have exi : X.Nonempty := ⟨x, h1⟩
    have sthm5 : Set.ncard X > 0 := by
      exact exi.ncard_pos sthm4
    omega
  · intro h2
    simp only [Set.setOf_false, Set.mem_empty_iff_false] at h2





/-
!INV# : Theorems regarding inverse timelines
INV0 - Each pair inside of T has its inverse as an
        element of the inverse timeline of T (and vice versa).
INV1 - The inverse pair of the inverse pair of any
        given element of a timeline is equal to the element itself.
F_INV0 - The inverse timeline of an inverse timeline of a timeline T is equal to T itself.
INV2 - If a timeline is valid, then it is nonbranching.
INV3 - If a timeline is nonbranching, then its inverse is nonbranching.
INV4 - If a timeline is ordered then its inverse is ordered.
INV5 - If a timeline is valid, then its inverse is nonempty.
INV6 - If a timeline is valid, then its inverse is strictly ordered.
F_INV1 - If a timeline is valid, then its inverse is valid.
INV7 - If a timeline is valid, then its inverse has its same field.
INV8 - If an ordered pair is an element of a valid timeline T, then its inverse pair is not in T
-/
theorem INV0 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  ∀ p, p ∈ τ ↔ inv_pair p ∈ inv_timeline τ := by
  unfold inv_pair
  unfold inv_timeline
  intro T I
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hp1
    exact ⟨I, hp1, rfl, rfl⟩
  · intro hp2
    rcases hp2 with ⟨q, hq, c1, c2⟩
    have hIq : I = q := Prod.ext c2 c1
    rw [hIq]
    exact hq

theorem INV1 {κ : Type T} {n : ℕ} :
  ∀ (p : timeline κ n × timeline κ n),
  (inv_pair (inv_pair p) = p) := by
  unfold inv_pair
  intro p
  rw []

theorem INV {κ : Type T} {n : ℕ} :
  ∀ (p q : timeline κ n × timeline κ n),
  inv_pair p = inv_pair q ↔ p = q := by
  intro p q
  constructor
  · intro hp1
    have sthm1 : inv_pair (inv_pair p) = inv_pair (inv_pair q) := by
      rw [hp1]
    have sthm2 := INV1 p
    have sthm3 := INV1 q
    rw [sthm2] at sthm1
    rw [sthm3] at sthm1
    exact sthm1
  · intro hp2
    rw [hp2]

theorem F_INV0 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  inv_timeline (inv_timeline τ) = τ := by
  intro T
  have thm1 : ∀ p ∈ T, inv_pair (inv_pair p) = p := by
    intro p hp
    exact INV1 p
  have thm2 : ∀ p, p ∈ T ↔ inv_pair (inv_pair p) ∈ inv_timeline (inv_timeline T) := by
    intro p
    have sthm1 := INV0 T p
    have sthm2 := INV0 (inv_timeline T) (inv_pair p)
    constructor
    · intro hp1
      have ssthm1 := sthm1.mp hp1
      have ssthm2 := sthm2.mp ssthm1
      exact ssthm2
    · intro hp2
      have ssthm1 := sthm2.mpr hp2
      have ssthm2 := sthm1.mpr ssthm1
      exact ssthm2
  have thm3 : ∀ p, p ∈ T ↔ p ∈ inv_timeline (inv_timeline T) := by
    exact thm2
  have finalthm : T = inv_timeline (inv_timeline T) := by
    ext p
    exact thm3 p
  exact finalthm.symm

theorem INV2 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  valid_timeline τ → nonbranching τ := by
  unfold valid_timeline
  intro T hp
  rcases hp with ⟨ha, hb, hc, hd⟩
  exact ha

theorem INV3 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  nonbranching τ → nonbranching (inv_timeline τ) := by
  unfold nonbranching
  intro T Tn p pi q qi
  let inv_q := inv_pair q
  let inv_p := inv_pair p
  have hq := INV0 T inv_q
  have hp := INV0 T inv_p
  have subp := INV1 inv_q
  have subq := INV1 inv_p
  have sub1 : inv_q ∈ T ↔ q ∈ inv_timeline T := by
    exact hq
  have sub2 : inv_p ∈ T ↔ p ∈ inv_timeline T := by
    exact hp
  have sub3 : inv_pair q ∈ T ↔ q ∈ inv_timeline T := by
    change inv_q ∈ T ↔ q ∈ inv_timeline T
    exact sub1
  have sub4 : inv_pair p ∈ T ↔ p ∈ inv_timeline T := by
    change inv_p ∈ T ↔ p ∈ inv_timeline T
    exact sub2
  have hh1 : inv_pair p ∈ T := by
    exact sub4.mpr pi
  have hh2 : inv_pair q ∈ T := by
    exact sub3.mpr qi
  have f : (inv_pair q).1 = (inv_pair p).1 ↔ (inv_pair q).2 = (inv_pair p).2 := by
    exact Tn (inv_pair q) hh2 (inv_pair p) hh1
  have eq1 : (inv_pair q).1 = q.2 := by
    rfl
  have eq2 : (inv_pair q).2 = q.1 := by
    rfl
  have eq3 : (inv_pair p).1 = p.2 := by
    rfl
  have eq4 : (inv_pair p).2 = p.1 := by
    rfl
  simpa [eq1, eq2, eq3, eq4, eq_comm] using f.symm

theorem INV4 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  ordered τ → ordered (inv_timeline τ) := by
  unfold ordered
  unfold single
  intro T
  intro P1
  rcases P1 with h1 | h2
  --First case of the proof (singletons)
  rcases h1 with ⟨h11, h12⟩
  have nonempty : ∃ p, p ∈ T := by
    exact h11
  rcases nonempty with ⟨pair, Hx⟩
  have sthm0 := INV0 T pair
  have sthm1 : (inv_timeline T).Nonempty := by
    have ssthm0 : (inv_pair pair) ∈ inv_timeline T := by
      exact sthm0.mp Hx
    exact ⟨inv_pair pair, ssthm0⟩
  have sthm2 : ∃ q, ∀ p, inv_pair p ∈ inv_timeline T ↔ p = q := by
    rcases h12 with ⟨X, Y⟩
    have ssthm4 : ∀ p, inv_pair p ∈ inv_timeline T ↔ p = X := by
      intro p
      have sssthm1 := INV0 T p
      have sssthm2 : p ∈ T ↔ p = X := by
        exact Y p
      constructor
      · intro hp1
        have shp1 := sssthm1.mpr hp1
        have shp2 := sssthm2.mp shp1
        exact shp2
      . intro hp2
        have shp1 := sssthm2.mpr hp2
        have shp2 := sssthm1.mp shp1
        exact shp2
    exact ⟨X, ssthm4⟩
  have sthm3 : ∃ q, ∀ p, p ∈ inv_timeline T ↔ p = q := by
    rcases sthm2 with ⟨Z, Y⟩
    let X := inv_pair Z
    have ssthm0 : ∀ p, inv_pair p = Z ↔ p = X := by
      intro p
      have sssthm1 := INV1 Z
      have sssthm2 := INV1 p
      dsimp [X]
      constructor
      · intro shp1
        rw [← sssthm2, shp1]
      · intro shp2
        rw[shp2, sssthm1]
    have ssthm1 : ∀ p, p ∈ inv_timeline T ↔ p = X := by
      intro p
      let r := inv_pair p
      have sssthm1 : inv_pair r ∈ inv_timeline T ↔ r = Z := by
        exact Y r
      have sssthm2 : inv_pair r = p := by
        rfl
      dsimp [r] at sssthm1
      have sssthm3 : p ∈ inv_timeline T ↔ inv_pair p = Z := by
        exact sssthm1
      have sssthm4 : p ∈ inv_timeline T ↔ p = X := by
        have ssssthm1 : inv_pair p = Z ↔ p = X := by
          exact ssthm0 p
        constructor
        · intro shp1
          have sshp1 := sssthm3.mp shp1
          have sshp2 := ssssthm1.mp sshp1
          exact sshp2
        · intro shp2
          have sshp1 := ssssthm1.mpr shp2
          have sshp2 := sssthm3.mpr sshp1
          exact sshp2
      exact sssthm4
    exact ⟨X, ssthm1⟩
  have thm1 : ordered (inv_timeline T) := by
    left
    unfold single
    constructor
    · exact sthm1
    · exact sthm3
  exact thm1
  --Second case: Non-singeltons
  right
  intro hp1
  have sthm1 : ∃ ℓ, ℓ ∈ inv_timeline T := by
    exact hp1
  have sthm2 : ∃ ℓ, ℓ ∈ T := by
    rcases sthm1 with ⟨ρ, hpp⟩
    have ssthm1 : inv_pair ρ ∈ T := by
      have sssthm1 := INV0 T (inv_pair ρ)
      have sssthm2 := INV1 ρ
      rw [sssthm2.symm] at hpp
      exact sssthm1.mpr hpp
    exact ⟨inv_pair ρ, ssthm1⟩
  have sthm3 : ∀ p ∈ T, ∃ q ∈ T, p ≠ q ∧ (p.1 = q.2 ∨ p.2 = q.1) := by
    exact h2 sthm2
  have sthm4 : ∀ p ∈ T, ∃ q ∈ T, inv_pair p ≠ inv_pair q ∧ (p.1 = q.2 ∨ p.2 = q.1) := by
    intro p
    rcases sthm2 with ⟨q, hq⟩
    intro hp2
    have ssthm3 := sthm3 p hp2
    rcases ssthm3 with ⟨r, hr⟩
    rcases hr with ⟨h1, h2, h3⟩
    have ssthm1 := (INV p r).mp
    have ssthm2 : p ≠ r → inv_pair p ≠ inv_pair r := mt ssthm1
    have ssthm4 : inv_pair p ≠ inv_pair r := by
      exact ssthm2 h2
    exact ⟨r, h1, ssthm4, h3⟩
  have sthm5 : ∀ (p q : timeline κ n × timeline κ n),
    (p.1 = q.2 ∨ p.2 = q.1) ↔ ((inv_pair p).1 = (inv_pair q).2 ∨ (inv_pair p).2 = (inv_pair q).1) := by
    intro p q
    have ssthm1 : p.1 = q.2 ↔ (inv_pair p).2 = (inv_pair q).1 := by
      unfold inv_pair
      rfl
    have ssthm2 : p.2 = q.1 ↔ (inv_pair p).1 = (inv_pair q).2 := by
      unfold inv_pair
      rfl
    constructor
    · intro shp1
      rcases shp1 with oshp11 | oshp12
      right
      rw [ssthm1] at oshp11
      exact oshp11
      left
      rw [ssthm2] at oshp12
      exact oshp12
    · intro shp2
      rcases shp2 with oshp11 | oshp12
      right
      rw [ssthm2.symm] at oshp11
      exact oshp11
      left
      rw [ssthm1.symm] at oshp12
      exact oshp12
  have sthm6 : ∀ p ∈ T, ∃ q ∈ T,
    (inv_pair p ≠ inv_pair q ∧ ((inv_pair p).1 = (inv_pair q).2 ∨ (inv_pair p).2 = (inv_pair q).1)) := by
    intro p
    intro shp1
    have ssthm1 := sthm4 p shp1
    rcases ssthm1 with ⟨r, hr⟩
    rcases hr with ⟨h1, h2, h3⟩
    have ssthm2 := sthm5 p r
    rw [ssthm2] at h3
    exact ⟨r, h1, h2, h3⟩
  intro p
  intro hp
  have sthm7 : p ∈ inv_timeline T ↔ inv_pair p ∈ T := by
    have ssthm1 := (INV0 T (inv_pair p)).symm
    have ssthm2 := INV1 p
    rw [ssthm2] at ssthm1
    exact ssthm1
  rw [sthm7] at hp
  have sthm8 := sthm6 (inv_pair p) hp
  rcases sthm8 with ⟨r, hr⟩
  rcases hr with ⟨h1, h2, h3⟩
  have sthm9 := INV0 T r
  rw [sthm9] at h1
  have sthm10 := INV1 p
  rw [sthm10] at h2
  rw [sthm10] at h3
  exact ⟨(inv_pair r), h1, h2, h3⟩

theorem INV5 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  valid_timeline τ → (inv_timeline τ).Nonempty := by
  unfold valid_timeline
  intro T hp
  rcases hp with ⟨h1, h2, h3, h4⟩
  have sthm1 : ∃ ℓ, ℓ ∈ T := by
    exact h4
  rcases sthm1 with ⟨r, hr⟩
  have sthm2 := (INV0 T r).mp hr
  exact ⟨inv_pair r, sthm2⟩

theorem INV6 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  valid_timeline τ → strictly_ordered (inv_timeline τ) := by
  unfold valid_timeline
  unfold strictly_ordered
  intro T hp
  rcases hp with ⟨h1, h2, h3, h4⟩
  intro B A p hp q hq
  have sthm1 := h3 A B (inv_pair p)
  have sthm2 := INV0 T (inv_pair p)
  have sthm3 := INV1 p
  rw [sthm3] at sthm2
  rw [sthm2] at sthm1
  have sthm4 := sthm1 hp (inv_pair q)
  have sthm5 := INV0 T (inv_pair q)
  have sthm6 := INV1 q
  rw [sthm6] at sthm5
  rw [sthm5] at sthm4
  have sthm7 := sthm4 hq
  have sthm8 : p.2 = A ∧ p.1 = B → q.1 ≠ A ∨ q.2 ≠ B := by
    have ssthm1 : ∀ (t : timeline κ n × timeline κ n),
      (inv_pair t).1 = t.2 := by
      unfold inv_pair
      intro p
      rfl
    have ssthm2 : ∀ (t : timeline κ n × timeline κ n),
      (inv_pair t).2 = t.1 := by
      unfold inv_pair
      intro p
      rfl
    rw [ssthm1 p] at sthm7
    rw [ssthm2 p] at sthm7
    rw [ssthm1 q] at sthm7
    rw [ssthm2 q] at sthm7
    exact sthm7
  intro fhp
  have sthm9 : p.1 = B ∧ p.2 = A → p.2 = A ∧ p.1 = B := by
    tauto
  have sthm10 := sthm9 fhp
  have sthm11 := sthm8 sthm10
  have sthm12 : q.1 ≠ A ∨ q.2 ≠ B ↔ q.2 ≠ B ∨ q.1 ≠ A := by
    exact or_comm
  rw [sthm12] at sthm11
  exact sthm11

theorem F_INV1 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  valid_timeline τ → valid_timeline (inv_timeline τ) := by
  unfold valid_timeline
  intro T hp
  have sthm1 := INV5 T hp
  have sthm2 := INV6 T hp
  rcases hp with ⟨h1, h2, h3, h4⟩
  have sthm3 := INV4 T h2
  have sthm4 := INV3 T h1
  exact ⟨sthm4, sthm3, sthm2, sthm1⟩

theorem INV7 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  valid_timeline τ → (ffld τ = ffld (inv_timeline τ)) := by
  intro T hT
  have sthm1 : ∀ p, p ∈ T → p.1 ∈ ffld T ∧ p.2 ∈ ffld T := by
    unfold ffld
    intro p hp
    rw [Set.mem_setOf_eq]
    rw [Set.mem_setOf_eq]
    have ssthm1 : T ∈ order_set n := by
      unfold order_set
      rw [Set.mem_setOf_eq]
      exact hT
    constructor
    · have sssthm1 : p.1 = p.1 ∨ p.2 = p.1 := by
        left
        rfl
      have sssthm2 : ∃ q ∈ T, q.1 = p.1 ∨ q.2 = p.1 := by
        exact ⟨p, hp, sssthm1⟩
      constructor
      · exact ssthm1
      · exact sssthm2
    · have sssthm1 : p.1 = p.2 ∨ p.2 = p.2 := by
        right
        rfl
      have sssthm2 : ∃ q ∈ T, q.1 = p.2 ∨ q.2 = p.2 := by
        exact ⟨p, hp, sssthm1⟩
      constructor
      · exact ssthm1
      · exact sssthm2
  unfold ffld
  have sthm2 : T ∈ order_set n ↔ (inv_timeline T) ∈ order_set n := by
    have ssthm1 := F_INV1 T
    have ssthm2 := F_INV1 (inv_timeline T)
    have ssthm3 := F_INV0 T
    rw [ssthm3] at ssthm2
    unfold order_set
    rw [Set.mem_setOf_eq]
    rw [Set.mem_setOf_eq]
    constructor
    · intro hp1
      exact ssthm1 hp1
    · intro hp2
      exact ssthm2 hp2
  have sthm3 : ∀ (p : timeline κ n × timeline κ n) (s : timeline κ n),
    (p.1 = s ∨ p.2 = s) ↔ ((inv_pair p).1 = s ∨ (inv_pair p).2 = s) := by
    intro p s
    have ssthm1 : (p.2, p.1).2 = p.1 := by
        rfl
    have ssthm2 : (p.2, p.1).1 = p.2 := by
        rfl
    constructor
    · intro hp1
      rcases hp1 with hp11 | hp12
      right
      unfold inv_pair
      rw [ssthm1]
      exact hp11
      left
      unfold inv_pair
      rw [ssthm2]
      exact hp12
    · intro hp2
      rcases hp2  with hp21 | hp22
      unfold inv_pair at hp21
      rw [ssthm2.symm]
      right
      exact hp21
      unfold inv_pair at hp22
      rw [ssthm1.symm]
      left
      exact hp22
  rw [sthm2]
  ext s
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hp1
    rcases hp1 with ⟨h1, h2⟩
    rcases h2 with ⟨X, hX⟩
    rcases hX with ⟨hX1, hX2⟩
    have ssthm1 := (INV0 T X).mp hX1
    have ssthm2 : ∃ p ∈ inv_timeline T, p.1 = s ∨ p.2 = s := by
      have sssthm1 := (sthm3 X s).mp hX2
      exact ⟨inv_pair X, ssthm1, sssthm1⟩
    constructor
    · exact h1
    · exact ssthm2
  · intro hp2
    rcases hp2 with ⟨h1, h2⟩
    rcases h2 with ⟨X, hX⟩
    rcases hX with ⟨hX1, hX2⟩
    have ssthm1 := (INV0 (inv_timeline T) X).mp hX1
    have eq := F_INV0 T
    rw [eq] at ssthm1
    have ssthm2 : ∃ p ∈ T, p.1 = s ∨ p.2 = s := by
      have sssthm1 := (sthm3 X s).mp hX2
      exact ⟨inv_pair X, ssthm1, sssthm1⟩
    constructor
    · exact h1
    · exact ssthm2

theorem INV8 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (p : timeline κ n × timeline κ n),
  (valid_timeline τ ∧ p ∈ τ) → inv_pair p ∉ τ := by
  intro T p hp
  rcases hp with ⟨hp1, hp2⟩
  have valid := hp1
  unfold valid_timeline at hp1
  rcases hp1 with ⟨h1, h2, h3, h4⟩
  unfold ordered at h2
  unfold nonbranching at h1
  have sthm1 := h1 p hp2 (inv_pair p)
  rcases h2 with h21 | h22
  unfold inv_pair
  unfold inv_pair at sthm1
  have sthm2 : (p.2, p.1) ∈ T → False := by
    intro hhp
    have ssthm1 := sthm1 hhp
    simp at ssthm1
    have ssthm1 : is_imm_succ p.2 p.1 T := by
      unfold is_imm_succ
      constructor
      · exact valid
      · have sssthm1 : p.1 = p.1 ∧ p.2 = p.2 := by
          constructor
          · rfl
          · rfl
        have sssthm2 : p ∈ T ∧ p.1 = p.1 ∧ p.2 = p.2 := by
          constructor
          · exact hp2
          · exact sssthm1
        exact ⟨p, sssthm2⟩
    have ssthm2 : is_imm_succ p.1 p.2 T := by
      unfold is_imm_succ
      constructor
      · exact valid
      · have sssthm1 : (p.2, p.1).1 = p.2 ∧ (p.2, p.1).2 = p.1 := by
          constructor
          · rfl
          · rfl
        have sssthm2 : (p.2, p.1) ∈ T ∧ (p.2, p.1).1 = p.2 ∧ (p.2, p.1).2 = p.1 := by
          constructor
          · exact hhp
          · exact sssthm1
        exact ⟨inv_pair p, sssthm2⟩
    have ssthm3 : p.2 ∈ succs p.1 T ∧ p.1 ∈ succs p.2 T := by
      unfold succs is_succ
      simp only [gt_iff_lt, ↓existsAndEq, and_true, Set.mem_setOf_eq]
      constructor
      · refine ⟨1, ?_, ?_⟩
        · omega
        · exact ssthm1
      · refine ⟨1, ?_, ?_⟩
        · omega
        · exact ssthm2
    have ssthm4 := transitivity n T p.1 p.2 p.1
    have ssthm5 : p.1 ∈ succs p.1 T := ssthm4 ssthm3
    have ssthm6 := irreflexivity n T p.1
    exact ssthm6 ssthm5
  contrapose sthm2
  push Not
  simp only [and_true]
  exact sthm2
  have sthm3 := h22 h4 p hp2
  have sthm4 : (p.2, p.1) ∈ T → False := by
    intro hhp
    have ssthm1 : is_imm_succ p.2 p.1 T := by
      unfold is_imm_succ
      constructor
      · exact valid
      · have sssthm1 : p.1 = p.1 ∧ p.2 = p.2 := by
          constructor
          · rfl
          · rfl
        have sssthm2 : p ∈ T ∧ p.1 = p.1 ∧ p.2 = p.2 := by
          constructor
          · exact hp2
          · exact sssthm1
        exact ⟨p, sssthm2⟩
    have ssthm2 : is_imm_succ p.1 p.2 T := by
      unfold is_imm_succ
      constructor
      · exact valid
      · have sssthm1 : (p.2, p.1).1 = p.2 ∧ (p.2, p.1).2 = p.1 := by
          constructor
          · rfl
          · rfl
        have sssthm2 : (p.2, p.1) ∈ T ∧ (p.2, p.1).1 = p.2 ∧ (p.2, p.1).2 = p.1 := by
          constructor
          · exact hhp
          · exact sssthm1
        exact ⟨inv_pair p, sssthm2⟩
    have ssthm3 : p.2 ∈ succs p.1 T ∧ p.1 ∈ succs p.2 T := by
      unfold succs is_succ
      simp only [gt_iff_lt, ↓existsAndEq, and_true, Set.mem_setOf_eq]
      constructor
      · refine ⟨1, ?_, ?_⟩
        · omega
        · exact ssthm1
      · refine ⟨1, ?_, ?_⟩
        · omega
        · exact ssthm2
    have ssthm4 := transitivity n T p.1 p.2 p.1
    have ssthm5 : p.1 ∈ succs p.1 T := ssthm4 ssthm3
    have ssthm6 := irreflexivity n T p.1
    exact ssthm6 ssthm5
  contrapose sthm4
  push Not
  simp only [and_true]
  exact sthm4

theorem F_INV2 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  valid_timeline τ ↔ valid_timeline (inv_timeline τ) := by
  intro T
  constructor
  · exact F_INV1 T
  · have temp := F_INV1 (inv_timeline T)
    rw [F_INV0 T] at temp
    exact temp





/-
!FLD# : Theorems regarding the field
FLD0 : The field of a valid timeline P, if P is a subset of another valid timeline T, is a subset
        of the field of T.
FLD1 :
-/
theorem FLD0 {κ : Type T} {n : ℕ} :
  ∀ (τ ρ: Set (timeline κ n × timeline κ n)),
  (valid_timeline τ ∧ valid_timeline ρ ∧ ρ ⊆ τ) → ffld ρ ⊆ ffld τ := by
  intro T P h
  rcases h with ⟨vT, vP, subPT⟩
  simp only [Set.subset_def]
  intro x hx
  simp only [Set.subset_def] at subPT
  unfold ffld
  simp only [Prod.exists, Set.mem_setOf_eq]
  constructor
  · unfold order_set
    simp only [Set.mem_setOf_eq]
    exact vT
  · unfold ffld at hx
    simp only [Prod.exists, Set.mem_setOf_eq] at hx
    rcases hx with ⟨hxv, hxe⟩
    unfold order_set at hxv
    simp only [Set.mem_setOf_eq] at hxv
    rcases hxe with ⟨y, z, hxef⟩
    rcases hxef with ⟨eps, eq⟩
    have sthm1 := subPT (y,z) eps
    exact ⟨y, z, sthm1, eq⟩





/-
!SP# : Theorems regarding successors and predecessors
SP0 : If a lower-order timeline B is an immediate successor of another lower-order timeline A
      within the field of some timeline T, then B is a succesor of A.
SP1 : If B is an immediate successor of A in T, then A is not an immediate successor of B in T.
SP2 :
SP3 :
SP4 :
SP5 :
SP6 :
-/
theorem SP0 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (A B : timeline κ n),
  is_imm_succ B A τ → B ∈ succs A τ := by
    unfold succs is_succ
    intro T A B hB
    simp only [gt_iff_lt, Set.mem_setOf_eq]
    refine ⟨1, ?_, ?_⟩
    omega
    exact hB

theorem SP1 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (A B : timeline κ n),
  (is_imm_succ A B τ) → ¬is_imm_succ B A τ := by
  intro T A B h
  have sthm2 := transitivity n T B A B
  have sthm3 := irreflexivity n T B
  have sthm4 : ¬ ((is_imm_succ A B T) → ¬is_imm_succ B A T) → False := by
    push Not
    intro hp
    have ssthm1 := SP0 T B A hp.1
    have ssthm2 := SP0 T A B hp.2
    have ssthm3 : A ∈ succs B T ∧ B ∈ succs A T := by
      constructor
      · exact ssthm1
      · exact ssthm2
    have ssthm4 := sthm2 ssthm3
    exact sthm3 ssthm4
  push Not at sthm4
  contrapose sthm4
  push Not
  simp only [and_true]
  constructor
  · exact h
  · exact sthm4

theorem SP2 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (A B : timeline κ n),
  B ∈ succs A τ → A ∉ succs B τ := by
  intro T A B hB
  have transit := transitivity n T A B A
  have irreflex := irreflexivity n T A
  have contra : A ∈ succs B T → False := by
    intro hyp
    have fhyp : B ∈ succs A T ∧ A ∈ succs B T := ⟨hB, hyp⟩
    have ssthm1 := transit fhyp
    exact irreflex ssthm1
  contrapose contra
  push Not
  simp only [and_true]
  exact contra

theorem SP3 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (A B : timeline κ n),
  A ∈ succs B τ → A ∈ ffld τ ∧ B ∈ ffld τ := by
  intro T A B hA
  unfold succs is_succ at hA
  simp only [Set.mem_setOf_eq] at hA
  rcases hA with ⟨x, gr, hx⟩
  induction x generalizing A B with
  | zero => simp at gr
  | succ x ih =>
    cases x with
    | zero =>
      simp only [zero_add] at hx
      unfold is_imm_succ at hx
      unfold ffld
      unfold order_set
      simp only [Set.mem_setOf_eq]
      rcases hx with ⟨hx1, X, HX1, HX2, HX3⟩
      have or1 : X.1 = B ∨ X.2 = B := by
        left
        exact HX2
      have or2 : X.1 = A ∨ X.2 = A := by
        right
        exact HX3
      constructor
      · refine ⟨hx1, ?_⟩
        exact ⟨X, HX1, or2⟩
      · refine ⟨hx1, ?_⟩
        exact ⟨X, HX1, or1⟩
    | succ nt =>
      simp only [gt_iff_lt, lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le, true_and] at hx
      simp only [gt_iff_lt, lt_add_iff_pos_left, add_pos_iff, Order.lt_two_iff, zero_le, or_true,
        Order.lt_add_one_iff, forall_const] at gr ih
      rcases hx with ⟨X, iS, iIS⟩
      unfold is_succ at iS
      have new1 := ih X B iS
      have new2 : A ∈ ffld T := by
        unfold ffld order_set
        simp only [Set.mem_setOf_eq]
        unfold is_imm_succ at iIS
        refine ⟨iIS.1, ?_⟩
        rcases iIS.2 with ⟨Y, hYB, hY1eq, hY2eq⟩
        use Y
        refine ⟨hYB, ?_⟩
        right
        exact hY2eq
      constructor
      · exact new2
      · exact new1.2

theorem valid_timeline_imp {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (A B : timeline κ n),
  B ∈ succs A τ → valid_timeline τ := by
  intro T A B BsA
  have temp := SP3 T B A BsA
  unfold ffld order_set at temp
  simp only [Set.mem_setOf_eq] at temp
  rcases temp with ⟨thm, rest⟩
  exact thm.1

theorem SP4 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (A B : timeline κ n),
  valid_timeline τ → (B ∈ succs A τ ↔ A ∈ preds B τ) := by
  intro T A B vT
  have tot := totality n T A B
  have irreflex := irreflexivity n T A
  constructor
  · intro hB
    have ffldmem := SP3 T B A hB
    have hyp : A ∈ ffld T ∧ B ∈ ffld T ∧ valid_timeline T := ⟨ffldmem.2, ffldmem.1, vT⟩
    have total := tot hyp
    unfold preds
    simp only [ne_eq, Set.mem_setOf_eq]
    refine ⟨ffldmem.2, ffldmem.1, ?_, ?_⟩
    have sthm1 := SP2 T A B hB
    exact sthm1
    have contra : A = B → False := by
      intro eq
      rw [eq.symm] at hB
      exact irreflex hB
    contrapose contra
    push Not
    simp only [and_true]
    exact contra
  · intro hA
    unfold preds at hA
    simp only [ne_eq, Set.mem_setOf_eq] at hA
    rcases hA with ⟨ffldA, ffldB, nsuccA, neq⟩
    have hyp : A ∈ ffld T ∧ B ∈ ffld T ∧ valid_timeline T := ⟨ffldA, ffldB, vT⟩
    have total := tot hyp
    rcases total with As | equ | Bs
    · exact False.elim (nsuccA As)
    · exact False.elim (neq equ)
    · exact Bs

theorem SP4R {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (A B : timeline κ n),
  B ∈ succs A τ → A ∈ preds B τ := by
  intro T A B BsA
  have vT := valid_timeline_imp T A B BsA
  exact (SP4 T A B vT).mp BsA

theorem fundirreflexivity {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  valid_timeline τ → ∀ (B : timeline κ n), B ∉ preds B τ := by
    intro T vT B
    exact (not_iff_not.mpr (SP4 T B B vT)).mp (irreflexivity n T B)

theorem fundtotality {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)) (B : timeline κ n),
  B ∈ ffld τ → valid_timeline τ → ffld τ = succs B τ ∪ {B} ∪ preds B τ := by
  intro T B BinF vT
  simp only [Set.ext_iff]
  intro x
  have tot := totality n T x B
  constructor
  · intro hp1
    replace tot := tot ⟨hp1, BinF, vT⟩
    simp only [Set.union_singleton, Set.mem_union, Set.mem_insert_iff]
    rcases tot with X | Y | Z
    left
    right
    exact X
    left
    left
    exact Y
    right
    exact ((SP4 T x B vT).mp Z)
  · intro hp2
    simp only [Set.union_singleton, Set.mem_union, Set.mem_insert_iff] at hp2
    rcases hp2 with X | Y
    rcases X with X1 | X2
    rw [X1.symm] at BinF
    exact BinF
    exact (SP3 T x B X2).1
    rw [(SP4 T x B vT).symm] at Y
    exact (SP3 T B x Y).2

theorem SP5 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (A B : timeline κ n),
  (is_imm_succ B A τ → is_imm_succ A B (inv_timeline τ)) := by
  intro T A B
  unfold is_imm_succ
  intro immSucc
  refine ⟨F_INV1 T immSucc.1, ?_⟩
  rcases immSucc.2 with ⟨X, Xin, hX⟩
  have triv : (X.1, X.2) ∈ T := Xin
  rw [hX.1, hX.2] at triv
  have invininvT := (INV0 T (A, B)).mp triv
  unfold inv_pair at invininvT
  simp only at invininvT
  simp only [Prod.exists, exists_eq_right_right, exists_eq_right]
  exact invininvT

theorem SP6 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  ∀ B ∈ ffld τ,
  valid_timeline τ →
  (succs B τ) = ∅ → ∀ A ∈ ffld τ, A ≠ B → A ∈ preds B τ := by
  intro T B Binf vT empt A Ainf AneB
  rw [Set.eq_empty_iff_forall_notMem] at empt
  replace empt := empt A
  have tot := totality n T A B
  simp only [and_imp] at tot
  replace tot := tot Ainf Binf vT
  simp only [or_iff_not_imp_left] at tot
  replace tot := tot empt AneB
  exact (SP4 T A B vT).mp tot

theorem SP7 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  ∀ B ∈ ffld τ,
  valid_timeline τ →
  (preds B τ) = ∅ → ∀ A ∈ ffld τ, A ≠ B → A ∈ succs B τ := by
  unfold preds
  intro T B Binf vT empt A Ainf AneB
  --simp [Set.mem_setOf_eq] at Ainf
  simp only [ne_eq] at empt
  rw [Set.eq_empty_iff_forall_notMem] at empt
  replace empt := empt A
  simp only [Set.sep_and, Set.mem_inter_iff, Set.mem_setOf_eq, not_and, not_not, and_imp] at empt
  replace empt := empt Ainf Binf Ainf
  contrapose empt
  push Not
  refine ⟨empt, Ainf, AneB⟩

theorem SP8 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (A : timeline κ n),
  succs A τ ∩ preds A τ = ∅ := by
  intro T A
  ext x
  unfold preds
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false,
            iff_false, not_and, ne_eq, Set.mem_setOf_eq]
  intro succx ffldx ffldA nffldx
  push Not
  have contra := nffldx succx
  contrapose contra
  push Not

theorem SP9 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  valid_timeline τ → ∀ p ∈ τ, p.1 ≠ p.2 := by
  intro T vT p pinT
  have irreflex := irreflexivity n T p.1
  have contra : p.1 = p.2 → False := by
    intro equ
    have temp : (p.1, p.2) ∈ T := by
      exact pinT
    have altin : (p.1, p.1) ∈ T := by
      rw [equ.symm] at temp
      exact temp
    have imm_succ : is_imm_succ p.1 p.1 T := by
      unfold is_imm_succ
      refine ⟨vT, ?_⟩
      simp only [Prod.exists, exists_eq_right_right, exists_eq_right]
      exact altin
    have ff : p.1 ∈ succs p.1 T := by
      exact SP0 T p.1 p.1 imm_succ
    exact irreflex ff
  contrapose! contra
  simp only [and_true]
  exact contra

theorem SP10 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  (∀ (A B : timeline κ n), (A, B) ∈ τ → ∃ (C : timeline κ n), (C, A) ∈ τ)
  → ∀ x ∈ ffld τ, ∃ y, y ∈ preds x τ := by
  intro T all x xinf
  have copy := xinf
  --rcases nemptyT with ⟨p, pinT⟩
  unfold ffld order_set at xinf
  simp only [Set.mem_setOf_eq] at xinf
  rcases xinf with ⟨vT, ⟨p, ⟨pinT, fir | sec⟩⟩⟩
  have ff : (x, p.2) ∈ T := by
    have pinTm : (p.1, p.2) ∈ T := pinT
    rw [fir] at pinTm
    exact pinTm
  replace all := all x p.2 ff
  rcases all with ⟨C, innT⟩
  have Cinf : C ∈ ffld T := by
    unfold ffld order_set
    simp only [Prod.exists, Set.mem_setOf_eq]
    refine ⟨vT, ?_⟩
    have temp : (C = C ∨ x = C) := by
      left
      rfl
    exact ⟨C, x, innT, temp⟩
  have tot := totality n T x C ⟨copy, Cinf, vT⟩
  have equiv := SP4 T C x vT
  rw [equiv] at tot
  have temp : C ∈ preds x T := by
    have neq := SP9 T vT (C, x) innT
    simp only at neq
    have nsucc : C ∈ succs x T → False := by
      have xinimmsuccs : is_imm_succ x C T := by
        unfold is_imm_succ
        refine ⟨vT, ?_⟩
        simp only [Prod.exists, exists_eq_right_right, exists_eq_right]
        exact innT
      have xinsuccs := SP0 T C x xinimmsuccs
      have irreflex := irreflexivity n T C
      intro Cinsuccs
      have transit := transitivity n T C x C ⟨xinsuccs, Cinsuccs⟩
      exact irreflex transit
    contrapose! nsucc
    aesop
  exact ⟨C, temp⟩
  have ff : (p.1, x) ∈ T := by
    have pinTm : (p.1, p.2) ∈ T := pinT
    rw [sec] at pinTm
    exact pinTm
  replace all := all p.1 x ff
  rcases all with ⟨C, innT⟩
  have neq := SP9 T vT p pinT
  rw [sec] at neq
  have predC : x ∈ succs C T := by
    --unfold succs is_succ
    --simp only [gt_iff_lt, Set.mem_setOf_eq]
    have isimmsucc1 : is_imm_succ p.1 C T := by
      unfold is_imm_succ
      refine ⟨vT, ?_⟩
      simp only [Prod.exists, exists_eq_right_right, exists_eq_right]
      exact innT
    have isimmsucc2 : is_imm_succ x p.1 T := by
      unfold is_imm_succ
      refine ⟨vT, ?_⟩
      simp only [Prod.exists, exists_eq_right_right, exists_eq_right]
      exact ff
    have issucc1 := SP0 T C p.1 isimmsucc1
    have issucc2 := SP0 T p.1 x isimmsucc2
    exact transitivity n T C p.1 x ⟨issucc1, issucc2⟩
  exact ⟨C, (SP4 T C x vT).mp predC⟩

theorem SP11 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  valid_timeline τ → ∀ (A B C : timeline κ n),
  ((B ∈ preds C τ ∧ A ∈ preds B τ) → A ∈ preds C τ) := by
  intro T vT y z x
  have transit := transitivity n T y z x
  intro hp
  have eq1 := SP4 T z x vT
  have eq2 := SP4 T y z vT
  have eq3 := SP4 T y x vT
  rw [eq1, eq2, eq3] at transit
  exact transit hp.symm

theorem SP12 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  valid_timeline τ → (∀ x y, x ∈ preds y τ → (preds x τ ⊆ preds y τ ∧ preds x τ ≠ preds y τ)) := by
  intro T vT x y xinPr
  have transit := fun (A : timeline κ n) => SP11 T vT A x y
  have irreflex := irreflexivity n T
  have eq1 := SP4 T x y vT
  have eq2 := SP4 T x x vT
  replace eq2 := not_iff_not.mpr eq2
  have claim : ∀ C, C ∈ preds x T → C ∈ preds y T := by
    intro C
    simp only [and_imp] at transit
    exact transit C xinPr
  simp only [Set.subset_def]
  refine ⟨claim, ?_⟩
  have neclaim : x = y → False := by
    rw [eq1.symm] at xinPr
    intro feq
    rw [feq] at xinPr
    exact irreflex y xinPr
  simp only [ne_eq, Set.ext_iff]
  push Not
  use x
  replace irreflex := irreflex x
  rw [eq2] at irreflex
  right
  exact ⟨irreflex, xinPr⟩

theorem SP13 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  valid_timeline τ → (∀ x y, x ∈ preds y τ → (preds x τ ⊂ preds y τ)) := by
  intro T vT x y xinP
  have claim := SP12 T vT x y xinP
  have nclaim : ¬ (preds y T ⊆ preds x T) := by
    simp only [Set.subset_def]
    push Not
    have examp := irreflexivity n T x
    have eq := not_iff_not.mpr (SP4 T x x vT)
    rw [eq] at examp
    exact ⟨x, xinP, examp⟩
  simp only [Set.ssubset_def]
  exact ⟨claim.1, nclaim⟩

theorem SP14 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  (∀ x y, x ∈ succs y τ → (succs x τ ⊂ succs y τ)) := by
  intro T x y xinP
  --rw [SP4 T y x vT] at xinP
  have vT := valid_timeline_imp T y x xinP
  have transit := fun (A : timeline κ n) => transitivity n T y x A
  have irreflex := irreflexivity n T
  have eq1 := SP4 T x y vT
  --replace eq2 := not_iff_not.mpr eq2
  have claim : ∀ C, C ∈ succs x T → C ∈ succs y T := by
    intro C
    simp only [and_imp] at transit
    exact transit C xinP
  simp only [Set.ssubset_def, Set.subset_def, not_forall]
  replace irreflex := irreflex x
  refine ⟨claim, ?_⟩
  exact ⟨x, xinP, irreflex⟩

theorem SP15 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  valid_timeline τ → ∀ (A B C : timeline κ n), (is_imm_succ A C τ ∧ is_imm_succ B C τ) → A = B := by
    intro T ⟨nbT, orderT, sorderT, nemptyT⟩ A B C
    unfold is_imm_succ
    unfold nonbranching at nbT
    simp only [Prod.exists, exists_eq_right_right, exists_eq_right]
    intro vT
    rcases vT with ⟨x, y, z⟩
    simp only [Prod.forall] at nbT
    replace nbT := (nbT C A x.2 C B z).mp
    simp only [forall_const] at nbT
    exact nbT

theorem SP16 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  ∀ (A B : timeline κ n),
  A ∈ succs B τ → succs A τ ⊆ succs B τ := by
    intro T A B hA
    simp only [Set.subset_def]
    intro x xinA
    have irreflex := irreflexivity n T x
    exact transitivity n T B A x ⟨hA, xinA⟩

theorem SP17 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  valid_timeline τ →
  ∀ (A B : timeline κ n),
  A ∈ ffld τ → succs A τ ⊆ succs B τ → preds B τ ⊆ preds A τ := by
  intro T vT A B Ainffld subsucc
  simp only [Set.subset_def] at subsucc
  simp only [Set.subset_def]
  intro x xinpredsB
  have claim := SP4 T B A vT
  have rewrite := (SP4 T x B vT).mpr xinpredsB
  have ffldb := (SP3 T B x rewrite).symm
  have transit := SP11 T vT x B A
  have nclaim : A = B ∨ B ∈ preds A T → x ∈ preds A T := by
    intro lor
    rcases lor with frst | scnd
    rw [frst]
    exact xinpredsB
    exact transit ⟨scnd, xinpredsB⟩
  have tot := totality n T A B ⟨Ainffld, ffldb.2, vT⟩
  rw [claim] at tot
  have negg : B ∉ succs A T := by
    intro inns
    replace subsucc := subsucc B inns
    exact (irreflexivity n T B) subsucc
  simp only [or_imp] at nclaim
  rcases tot with X | Y | Z
  · exact nclaim.2 X
  · exact nclaim.1 Y
  · contradiction

theorem SP18 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (A B : timeline κ n),
  B ∈ succs A τ → ∃ X, is_imm_succ X A τ := by
  intro T A B Binsucc
  unfold succs at Binsucc
  simp only [Set.mem_setOf_eq] at Binsucc
  rcases Binsucc with ⟨m, hm, mhm⟩
  induction m generalizing B with
  | zero =>
    omega
  | succ m ih =>
    cases m with
    | zero =>
      exact ⟨B, mhm⟩
    | succ k =>
      rcases mhm with ⟨M, L, J⟩
      exact ih L M J.1

theorem valid_timeline_imp_set1 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)) (A : timeline κ n),
  (succs A τ).Nonempty → valid_timeline τ := by
  intro T A nemptySA
  simp only [Set.nonempty_def] at nemptySA
  rcases nemptySA with ⟨x, xinSA⟩
  exact valid_timeline_imp T A x xinSA

theorem SP19 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  ∀ (A B : timeline κ n), is_imm_succ B A τ →
  succs A τ = succs B τ ∪ {B} := by
  intro T A B immSucc
  have vT := valid_timeline_imp T A B (SP0 T A B immSucc)
  have isSucc := SP0 T A B immSucc
  have fflds := SP3 T B A isSucc
  have subb := SP16 T B A isSucc
  simp only [Set.subset_def] at subb
  simp only [Set.ext_iff, Set.union_def, Set.mem_setOf_eq, Set.mem_singleton_iff]
  intro x
  have transit := transitivity n T A B x
  constructor
  · intro hh
    unfold succs at hh
    simp only [Set.mem_setOf_eq] at hh
    rcases hh with ⟨m, mg, succa⟩
    induction m generalizing x with
    | zero =>
      omega
    | succ m ih =>
      cases m with
      | zero =>
        right
        have eqr := SP15 T vT B x A
        exact (eqr ⟨immSucc, succa⟩).symm
      | succ k =>
        rcases succa with ⟨M, L, J⟩
        have temp := ih L
        replace subb := subb L
        have tt : B ∈ succs A T ∧ L ∈ succs B T → L ∈ succs A T := by
          intro hp
          exact subb hp.2
        replace temp := temp tt M J.1
        have LinS := SP0 T L x J.2
        rcases temp with h1 | h2
        left
        exact transitivity n T B L x ⟨h1, LinS⟩
        rw [h2] at LinS
        left
        exact LinS
  · intro hor
    rcases hor with ht | hy
    exact transit ⟨isSucc, ht⟩
    rw [hy.symm] at isSucc
    exact isSucc

theorem SP20 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  ∀ (A B : timeline κ n),
  is_imm_succ B A τ → succs A τ ∩ preds B τ = ∅ := by
  intro T A B immSuccB
  have vT := valid_timeline_imp T A B (SP0 T A B immSuccB)
  have claim := SP19 T A B immSuccB
  have empt := SP8 T B
  have irreflex := fundirreflexivity T vT B
  rw [claim]
  simp only [Set.union_inter_distrib_right]
  rw [empt]
  simp only [Set.empty_union, Set.singleton_inter_eq_empty]
  exact irreflex

theorem SP21 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  (valid_timeline τ ∧ (ffld τ).Finite) → (∀ x y, is_imm_succ y x τ → (succs y τ).ncard + 1 = (succs x τ).ncard) := by
  intro T ⟨vT, finfld⟩ x y ysx
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = (succs x T).ncard := by
    exact ⟨(succs x T).ncard, rfl⟩
  have yssx := SP0 T x y ysx
  have claim := SP14 T y x yssx
  have extclaim := SP16 T y x yssx
  replace extclaim := SP17 T vT y x (SP3 T y x yssx).1 extclaim
  have irreflexy := irreflexivity n T y
  have irreflexx := irreflexivity n T x
  have transit := fun (A : timeline κ n) => transitivity n T A x y
  have exisx : ∃ z, z ∈ succs x T ∧ z ∉ succs y T := ⟨y, yssx, irreflexy⟩
  have cclaim : ∀ z ∈ succs x T, z ∉ succs y T ↔ z = y := by
    intro z hz
    constructor
    · intro nins
      have zinffld := (SP3 T z x hz).1
      have yinffld := (SP3 T y x yssx).1
      have tot := totality n T z y ⟨zinffld, yinffld, vT⟩
      have ntot : y ∈ succs z T ∨ z = y := (tot.resolve_left nins).symm
      simp [or_iff_not_imp_left] at ntot
      unfold is_imm_succ at ysx
      have sclaim := ysx.2
      have negs : ¬ ∃ r, r ∈ succs x T ∧ r ∈ preds y T := by
        push Not
        intro r rins
        unfold succs at rins
        simp only [gt_iff_lt, Set.mem_setOf_eq] at rins
        unfold is_succ at rins
        rcases rins with ⟨m, mpos, hrm⟩
        cases m with
        | zero =>
          omega
        | succ m =>
          cases m with
          | zero =>
            have hrx : is_imm_succ r x T := by
              simpa using hrm
            have imp := (SP15 T vT r y x ⟨hrx, ysx⟩)
            have eq := not_iff_not.mpr (SP4 T y y vT)
            rw [eq] at irreflexy
            nth_rewrite 2 [← imp] at irreflexy
            exact irreflexy
          | succ =>
            rename_i k
            have ssclaim := hrm.2
            have transstep : ∃ X, X ∈ succs x T ∧ is_imm_succ r X T := by
              unfold succs
              simp only [Set.mem_setOf_eq]
              rcases ssclaim with ⟨X, B⟩
              refine ⟨X, ?_, B.2⟩
              exact ⟨k + 1, by omega, B.1⟩
            have rrinsx : r ∈ succs x T := by
              rcases transstep with ⟨X, hX, hr⟩
              have rimm := SP0 T X r hr
              exact transitivity n T x X r ⟨hX, rimm⟩
            have ex := (not_iff_not.mpr (SP4 T r x vT)).mp
            have new := ex (SP2 T x r rrinsx)
            have rinff := (SP3 T r x rrinsx).1
            have neq : r ≠ x := by
              intro eqq
              rw [eqq] at rrinsx
              exact irreflexx rrinsx
            have jjj : r ∈ preds y T → r = x ∨ r ∈ preds x T := by
              intro hp
              simp only [or_iff_not_imp_left]
              intro neq
              sorry
            sorry
      sorry
    · intro eqq
      rw [eqq]
      exact irreflexy
  sorry

theorem SP22 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)) (A B : timeline κ n),
  τ.Finite → is_imm_succ B A τ → (succs A τ).ncard = (succs B τ).ncard + 1 := by
  intro T A B Tfin BisA
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = (succs A T).ncard := by
    exact ⟨(succs A T).ncard, rfl⟩
  sorry


theorem SP23 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)) (B : timeline κ n),
  B ∈ ffld τ → valid_timeline τ →
  succs B τ ∪ {B} ∪ preds B τ =
  succs B (inv_timeline τ) ∪ {B} ∪ preds B (inv_timeline τ) := by
  intro T B BinF vT
  have totT := fundtotality T B BinF vT
  have ffldeq := INV7 T vT
  have BininvF : B ∈ ffld (inv_timeline T) := by
    rw [ffldeq] at BinF
    exact BinF
  have vinvT := F_INV1 T vT
  have totinvT := fundtotality (inv_timeline T) B BininvF vinvT
  rw [ffldeq.symm] at totinvT
  rw [totinvT] at totT
  exact totT.symm

theorem SP24 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (A B : timeline κ n),
  is_imm_succ B A τ → preds B τ = preds A τ  ∪ {A} := by
  intro T A B BisA
  have vT := valid_timeline_imp T A B (SP0 T A B BisA)
  have claim := SP19 T A B BisA
  have BsA := SP0 T A B BisA
  have subb := SP16 T B A BsA
  have totA := fundtotality T A (SP3 T B A BsA).2 vT
  have totB := fundtotality T B (SP3 T B A BsA).1 vT
  rw [claim.symm] at totB
  have inter := SP8 T B
  have subpred := SP17 T vT B A (SP3 T B A BsA).1 subb
  have subbb : succs A T ∩ preds B T = ∅ := by
    rw [claim]
    simp only [Set.inter_def, Set.empty_def, Set.ext_iff, Set.mem_setOf_eq, Set.union_def]
    intro y
    constructor
    · intro h
      rcases h.1 with h1 | h2
      simp only [Set.inter_def, Set.empty_def, Set.ext_iff, Set.mem_setOf_eq] at inter
      replace inter := inter y
      exact inter.mp ⟨h1, h.2⟩
      simp only [Set.mem_singleton_iff] at h2
      rw [h2] at h
      exact (fundirreflexivity T vT B) h.2
    · intro hf
      exact and_iff_not_or_not.mpr fun a ↦ hf
  simp only [Set.subset_def] at subpred
  have subp : preds A T ∪ {A} ⊆ preds B T := by
    simp only [Set.subset_def, Set.mem_union, Set.mem_singleton_iff]
    intro x hAx
    rcases hAx with M | J
    exact subpred x M
    rw [SP4 T A B vT, J.symm] at BsA
    exact BsA
  have new : succs A T ∩ (preds A T ∪ {A}) = ∅ := by
    simp only [Set.inter_def, Set.empty_def, Set.ext_iff, Set.mem_setOf_eq, Set.union_def]
    intro y
    simp only [Set.inter_def, Set.empty_def, Set.ext_iff, Set.mem_setOf_eq] at inter
    replace inter := inter y
    simp only [Set.union_def, Set.subset_def, Set.mem_setOf_eq] at subp
    replace subp := subp y
    constructor
    · intro h
      replace subp := subp h.2
      rw [claim] at h
      simp only [Set.union_def, Set.mem_setOf_eq, Set.mem_singleton_iff] at h
      rcases h.1 with h1 | h2
      exact inter.mp ⟨h1, subp⟩
      rw [h2] at subp
      exact (fundirreflexivity T vT B) subp
    · intro hf
      exact and_iff_not_or_not.mpr fun a ↦ hf
  rw [totB] at totA
  have dB : Disjoint (preds B T) (succs A T) := by
    simp only [Set.inter_comm] at subbb
    exact Set.disjoint_iff_inter_eq_empty.mpr subbb
  have dA : Disjoint (preds A T ∪ {A}) (succs A T) := by
    rw [Set.inter_comm (succs A T) (preds A T ∪ {A})] at new
    exact Set.disjoint_iff_inter_eq_empty.mpr new
  have equ : (succs A T ∪ preds B T) \ succs A T =
              (succs A T ∪ {A} ∪ preds A T) \ succs A T
      := congr_arg (· \ succs A T) totA
  simp only [Set.union_sdiff_left] at equ
  rw [Set.union_comm] at equ
  rw [Set.union_comm (succs A T) {A}] at equ
  rw [← Set.union_assoc] at equ
  simp only [Set.union_sdiff_right] at equ
  rw [dB.sdiff_eq_left, dA.sdiff_eq_left] at equ
  exact equ

theorem SP25 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)) (A B : timeline κ n),
  is_imm_succ B A τ → (A, B) ∈ τ := by
  intro T A B BisA
  unfold is_imm_succ at BisA
  rcases BisA.2 with ⟨X, XinT, hX⟩
  have claim : (X.1, X.2) ∈ T := XinT
  rw [hX.1, hX.2] at claim
  exact claim

theorem SP26 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (A B : timeline κ n),
  (B ∈ succs A τ → A ∈ succs B (inv_timeline τ)) := by
  intro T A B BinS
  have vT := valid_timeline_imp T A B BinS
  have invvT := F_INV1 T vT
  rcases SP18 T A B BinS with ⟨X, XisA⟩
  have XsA := SP0 T A X XisA
  have AisX := SP5 T A X XisA
  have AsX := SP0 (inv_timeline T) X A AisX
  have pairin : (A, X) ∈ T := SP25 T A X XisA
  unfold succs at BinS
  rcases BinS with ⟨m, mgz, hm⟩
  induction m generalizing B with
  | zero =>
    omega
  | succ m ih =>
    cases m with
    | zero =>
      rcases hm.2 with ⟨R, hR⟩
      have tem := validnonbranching T vT
      unfold nonbranching at tem
      replace tem := (tem R hR.1 (A, X) pairin).mp hR.2.1
      simp only at tem
      rw [tem] at hR
      rw [hR.2.2.symm]
      exact AsX
    | succ k =>
      rcases hm with ⟨M, L, J⟩
      have temp := ih L M J.1
      have inv := SP5 T L B J.2
      have BsL := SP0 (inv_timeline T) B L inv
      exact transitivity n (inv_timeline T) B L A ⟨BsL, temp⟩

theorem SP27 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (A B : timeline κ n),
  (B ∈ succs A (inv_timeline τ) ↔ A ∈ succs B τ) := by
  intro T A B
  constructor
  · intro hp
    have first := SP26 (inv_timeline T) A B hp
    rw [F_INV0 T] at first
    exact first
  · exact SP26 T B A

theorem valid_timeline_imp_preds {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (A B : timeline κ n),
  B ∈ preds A τ → valid_timeline τ := by
  intro T A B BpA
  unfold preds ffld order_set at BpA
  simp only [Set.mem_setOf_eq] at BpA
  rcases BpA with ⟨H, J⟩
  exact H.1

theorem SP4RR {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (A B : timeline κ n),
  B ∈ succs A τ ↔ A ∈ preds B τ := by
  intro T A B
  have vT := valid_timeline_imp_preds T B A
  constructor
  · exact SP4R T A B
  · intro ApB
    replace vT := vT ApB
    exact (SP4 T A B vT).mpr ApB

theorem SP27R {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (A B : timeline κ n),
  (B ∈ succs A (inv_timeline τ) ↔ B ∈ preds A τ) := by
  intro T A B
  rw [(SP4RR T B A).symm]
  exact SP27 T A B

theorem SP28 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)) (A : timeline κ n),
  valid_timeline τ → A ∈ ffld τ → succs A τ ∩ {A} = ∅ := by
  intro T A vT Ainf
  simp only [Set.inter_singleton_eq_empty]
  exact irreflexivity n T A

theorem SP29 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)) (A : timeline κ n),
  valid_timeline τ → A ∈ ffld τ → preds A τ ∩ {A} = ∅ := by
  intro T A vT Ainf
  simp only [Set.inter_singleton_eq_empty]
  exact fundirreflexivity T vT A

theorem SP30 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  τ.Finite → (ffld τ).Finite := by
  intro T Tfin
  unfold ffld order_set
  simp only [Set.mem_setOf_eq, Prod.exists]
  refine ((Tfin.image Prod.fst).union (Tfin.image Prod.snd)).subset ?_
  intro s hs
  rcases hs with ⟨_, a, b, hab, ha | hb⟩
  · exact Or.inl ⟨(a, b), hab, ha⟩
  · exact Or.inr ⟨(a, b), hab, hb⟩

theorem SP31 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)) (A B : timeline κ n),
  is_imm_succ B A τ → τ.Finite → (succs A τ).ncard = (succs B τ).ncard + 1 := by
  intro T A B BisA Tfin
  have claim := SP19 T A B BisA
  have finfld := SP30 T Tfin
  have subbstep := fun (X : timeline κ n) => SP3 T X B
  have subb : ∀ X ∈ succs B T, X ∈ ffld T := by
    intro X Xin
    exact (subbstep X Xin).1
  rw [Set.subset_def.symm] at subb
  have finsuccB : (succs B T).Finite := finfld.subset subb
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = (succs A T).ncard := by
    exact ⟨(succs A T).ncard, rfl⟩
  have vT := valid_timeline_imp T A B (SP0 T A B BisA)
  have disj := SP28 T B vT (SP3 T B A (SP0 T A B BisA)).1
  have bcard : ({B} : Set (timeline κ n)).ncard = 1 := by
    simp only [Set.ncard_singleton]
  have rdisj : Disjoint (succs B T) ({B}) := Set.disjoint_iff_inter_eq_empty.mpr disj
  have equ : (succs A T).ncard = (succs B T ∪ {B}).ncard := congr_arg Set.ncard claim
  have sbcard : (succs B T ∪ {B}).ncard = (succs B T).ncard + 1 := by
    rw [Set.ncard_union_eq rdisj
    (hs := finsuccB)
    (ht := Set.finite_singleton B), bcard]
  rw [equ.symm] at sbcard
  exact sbcard

theorem SP31R {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)) (A B : timeline κ n),
  is_imm_succ B A τ → τ.Finite → (preds B τ).ncard = (preds A τ).ncard + 1 := by
  intro T A B BisA finT
  have newset := SP24 T A B BisA
  have finffld := SP30 T finT
  have vT := valid_timeline_imp T A B (SP0 T A B BisA)
  have ABinf := (SP3 T B A (SP0 T A B BisA))
  have disj : Disjoint (preds A T) {A} := Set.disjoint_iff_inter_eq_empty.mpr (SP29 T A vT ABinf.2)
  have totB := (fundtotality T B ABinf.1 vT)
  have subbB : preds B T ⊆ ffld T := by
    rw [totB]
    exact Set.subset_union_right
  have totA := (fundtotality T A ABinf.2 vT)
  have subbA : preds A T ⊆ ffld T := by
    rw [totA]
    exact Set.subset_union_right
  have Acard : ({A} : Set (timeline κ n)).ncard = 1 := by
    exact Set.ncard_singleton A
  have finPredsB : (preds B T).Finite := by
    exact Set.Finite.subset finffld subbB
  have finPredsA : (preds A T).Finite := by
    exact Set.Finite.subset finffld subbA
  have finA : ({A} : Set (timeline κ n)).Finite := by
    exact Set.finite_singleton A
  have eqcard : (preds B T).ncard = (preds A T ∪ {A}).ncard :=
    congr_arg Set.ncard newset
  have equ : (preds A T ∪ {A}).ncard = (preds A T).ncard +
                ({A} : Set (timeline κ n)).ncard := by
    exact Set.ncard_union_eq disj finPredsA finA
  rw [equ, Acard] at eqcard
  exact eqcard

theorem SP32 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)) (A : timeline κ n),
  A ∈ ffld τ → τ.Finite → (ffld τ).ncard = (succs A τ).ncard + 1 + (preds A τ).ncard := by
  intro T A Ainf Tfin
  unfold ffld order_set at Ainf
  simp only [Set.mem_setOf_eq] at Ainf
  have vT := Ainf.1
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = (succs A T).ncard := by
    exact ⟨(succs A T).ncard, rfl⟩
  have tot := fundtotality T A Ainf vT
  sorry

theorem SP33 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)) (x y : timeline κ n),
  y ∈ succs x τ → ∃ z, is_imm_succ y z τ := by
  intro T x y ysux
  unfold succs at ysux
  simp only [Set.mem_setOf_eq] at ysux
  rcases ysux with ⟨m, mgz, imm⟩
  cases m with
  | zero =>
    omega
  | succ m =>
    cases m with
    | zero =>
      rw [zero_add] at mgz imm
      unfold is_succ at imm
      exact ⟨x, imm⟩
    | succ k =>
      rcases imm.2 with ⟨X, hX⟩
      exact ⟨X, hX.2⟩

theorem SP34 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)) (x y : timeline κ n),
  y ∈ preds x τ → ∃ z, is_imm_succ x z τ := by
  intro T x y ypredx
  have vT := valid_timeline_imp_preds T x y ypredx
  have xsuy := (SP4RR T y x).mpr ypredx
  exact SP33 T y x xsuy

theorem SP34R {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)) (x : timeline κ n),
  (preds x τ).Nonempty → ∃ z, is_imm_succ x z τ := by
  intro T x nemptyP
  simp only [Set.nonempty_def] at nemptyP
  rcases nemptyP with ⟨y, hy⟩
  exact SP34 T x y hy

theorem SP35 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)) (A B : timeline κ n),
  is_imm_succ B A τ → (preds B τ).Finite → (preds B τ).ncard = (preds A τ).ncard + 1 := by
  intro T A B BisA finPredsB
  have newset := SP24 T A B BisA
  have vT := valid_timeline_imp T A B (SP0 T A B BisA)
  have succ := SP0 T A B BisA
  have ABinf := (SP3 T B A (SP0 T A B BisA))
  have disj : Disjoint (preds A T) {A} := Set.disjoint_iff_inter_eq_empty.mpr (SP29 T A vT ABinf.2)
  have temp := SP16 T B A succ
  have subbA := SP17 T vT B A ABinf.1 temp
  have Acard : ({A} : Set (timeline κ n)).ncard = 1 := by
    exact Set.ncard_singleton A
  have finPredsA : (preds A T).Finite := by
    exact Set.Finite.subset finPredsB subbA
  have finA : ({A} : Set (timeline κ n)).Finite := by
    exact Set.finite_singleton A
  have eqcard : (preds B T).ncard = (preds A T ∪ {A}).ncard :=
    congr_arg Set.ncard newset
  have equ : (preds A T ∪ {A}).ncard = (preds A T).ncard +
                ({A} : Set (timeline κ n)).ncard := by
    exact Set.ncard_union_eq disj finPredsA finA
  rw [equ, Acard] at eqcard
  exact eqcard

theorem SP36 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)), ∀ x ∈ ffld τ,
  valid_timeline τ → ((preds x τ).Finite → ∃ z, preds z τ = ∅ ∧ z ∈ ffld τ) := by
  intro T x xinfld vT finpreds
  have subsetcl := fun (y : timeline κ n) => SP13 T vT y x
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = (preds x T).ncard := by
    exact ⟨(preds x T).ncard, rfl⟩
  induction m generalizing x with
  | zero =>
    replace hm := hm.symm
    simp only [Set.ncard_eq_zero finpreds] at hm
    exact ⟨x, hm, xinfld⟩
  | succ k ih =>
    replace hm := hm.symm
    have temp := ih
    have o : 0 < k + 1 :=
      by omega
    rw [hm.symm] at o
    have nemptyP : (preds x T).Nonempty := by
      exact (Set.natCard_pos finpreds).mp o
    have exi := SP34R T x nemptyP
    rcases exi with ⟨Z, hZ⟩
    have xsZ := SP0 T Z x hZ
    have claim1 := SP35 T Z x hZ finpreds
    have claim2 : (preds Z T).ncard = k := by
      rw [hm] at claim1
      exact Eq.symm (Nat.add_right_cancel claim1)
    replace claim2 := claim2.symm
    have subb := SP16 T x Z xsZ
    have fsubb := SP17 T vT x Z (SP3 T x Z xsZ).1 subb
    have finPredsZ : (preds Z T).Finite := by
      exact Set.Finite.subset finpreds fsubb
    have tt := fun (y : timeline κ n) => SP13 T vT y Z
    have Zinffld := (SP3 T x Z xsZ).2
    have test := ih Z Zinffld finPredsZ tt claim2
    exact test

theorem valid_timeline_imp_set2 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)) (x : timeline κ n),
  (preds x τ).Nonempty → valid_timeline τ := by
  intro T x nempty
  rcases nempty with ⟨y , hy⟩
  exact valid_timeline_imp_preds T x y hy

theorem SP3R {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)) (x y : timeline κ n),
  x ∈ preds y τ → x ∈ ffld τ ∧ y ∈ ffld τ := by
  intro T x y xpy
  exact (SP3 T y x ((SP4RR T x y).symm.mp xpy)).symm

theorem SP36R {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)) (x : timeline κ n),
  ((preds x τ).Nonempty → (preds x τ).Finite → ∃ z, preds z τ = ∅ ∧ z ∈ ffld τ) := by
  intro T x nempty finpreds
  have vT := valid_timeline_imp_set2 T x nempty
  rcases nempty with ⟨z, hz⟩
  have f := (SP4RR T z x).symm.mp hz
  exact SP36 T x (SP3R T z x hz).2 vT finpreds

theorem SP37 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)), ∀ x ∈ ffld τ,
  preds x τ ⊆ ffld τ := by
  intro T x xinf
  have vT : valid_timeline T := by
    unfold ffld order_set at xinf
    simp only [Set.mem_setOf_eq] at xinf
    exact xinf.1
  have tot := fundtotality T x xinf vT
  rw [tot]
  simp only [Set.subset_union_right]

theorem SP38 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)), ∀ x ∈ ffld τ,
  (ffld τ).Finite → (preds x τ).Finite := by
  intro T x xin finffld
  have subb := SP37 T x xin
  exact Set.Finite.subset finffld subb

theorem SP39 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  valid_timeline τ →
  ((ffld τ).Nonempty ↔ τ.Nonempty) := by
  intro T vT
  constructor
  · intro n1
    rcases n1 with ⟨x, hx⟩
    unfold ffld order_set at hx
    simp only [Set.mem_setOf_eq] at hx
    rcases hx.2 with ⟨X, hX⟩
    exact ⟨X, hX.1⟩
  · intro n2
    rcases n2 with ⟨x, hx⟩
    unfold ffld order_set
    simp only [Set.mem_setOf_eq, Prod.exists]
    have claim : (x.1, x.2) ∈ T := hx
    have triv : x.1 = x.1 ∨ x.2 = x.1 := by
      left
      rfl
    have cll : ∃ a b, (a, b) ∈ T ∧ (a = x.1 ∨ b = x.1) := by
      exact ⟨x.1, x.2, claim, triv⟩
    exact ⟨x.1, vT, cll⟩

theorem SPINFINITY {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  (ffld τ).Nonempty → ((∀ x ∈ ffld τ, ∃ y, y ∈ preds x τ)) → ¬ (τ.Finite) := by
  intro T nempty
  contrapose!
  intro Tfin
  have lor : (ffld T).Nonempty ∨ (ffld T) = ∅ := by
    exact Or.symm (Set.eq_empty_or_nonempty (ffld T))
  rcases nempty with ⟨X, XinT⟩
  have slor : (preds X T).Nonempty ∨ (preds X T) = ∅ := by
    exact Or.symm (Set.eq_empty_or_nonempty (preds X T))
  rcases slor with pnempty | pempty
  have finffld := SP30 T Tfin
  have case1 := SP36R T X pnempty (SP38 T X XinT finffld)
  rcases case1 with ⟨z, hz⟩
  simp only [Set.not_nonempty_iff_eq_empty.symm, Set.nonempty_def] at hz
  push Not at hz
  exact ⟨z, hz.2, hz.1⟩
  simp only [Set.not_nonempty_iff_eq_empty.symm, Set.nonempty_def] at pempty
  push Not at pempty
  exact ⟨X, XinT, pempty⟩




/-
!FL# : Theorems regarding the the definition of lasteles and firsteles
-/
theorem FL0 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)), ∀ x ∈ ffld τ,
  x ∈ firsteles τ ↔ preds x τ = ∅ := by
  intro T x xinf
  unfold firsteles
  simp only [Set.not_nonempty_iff_eq_empty.symm, Set.nonempty_def, not_exists,
              Set.mem_setOf_eq]
  have vT : valid_timeline T := by
    unfold ffld order_set at xinf
    simp only [Set.mem_setOf_eq] at xinf
    exact xinf.1
  constructor
  · contrapose
    push Not
    intro h1
    rcases h1 with ⟨y, hy⟩
    have exi := SP34 T x y hy
    rcases exi with ⟨z, hz⟩
    unfold is_imm_succ at hz
    replace hz := hz.2
    rcases hz with ⟨p, hp1, hp2, hp3⟩
    intro extra
    exact ⟨p, hp1, hp3⟩
  · contrapose
    push Not
    intro h2
    replace h2 := h2 xinf
    simp only [Prod.exists] at h2
    rcases h2 with ⟨a, b, pre, equ, final⟩
    have triv : a = a ∧ x = x := by
      exact Prod.mk_inj.mp rfl
    have claim : is_imm_succ x a T := by
      unfold is_imm_succ
      refine ⟨vT, ?_⟩
      simp only [Prod.exists, exists_eq_right_right, exists_eq_right]
      exact pre
    have pred := (SP4RR T a x).mp (SP0 T a x claim)
    exact Exists.intro a pred

theorem FL1 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)) (x : timeline κ n),
  x ∈ firsteles τ → ∃ p ∈ τ, p.1 = x := by
  intro T x
  unfold firsteles
  simp only [Set.mem_setOf_eq, and_imp]
  intro xinf h
  unfold ffld order_set at xinf
  simp only [Set.mem_setOf_eq] at xinf
  rcases xinf.2 with ⟨p, pinT, por⟩
  replace h := h p pinT
  replace por := por.symm
  simp only [or_iff_not_imp_left] at por
  push Not at por
  replace por := por h
  exact ⟨p, pinT, por⟩

theorem FL2 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)) (x : timeline κ n),
  x ∈ lasteles τ → ∃ p ∈ τ, p.2 = x := by
  intro T x
  unfold lasteles
  simp only [Set.mem_setOf_eq, and_imp]
  intro xinf h
  unfold ffld order_set at xinf
  simp only [Set.mem_setOf_eq] at xinf
  rcases xinf.2 with ⟨p, pinT, por⟩
  replace h := h p pinT
  replace por := por.symm
  simp only [or_iff_not_imp_right] at por
  push Not at por
  replace por := por h
  exact ⟨p, pinT, por⟩

theorem FL3 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  ((valid_timeline τ) → τ.Finite → ∃ x, x ∈ firsteles τ) := by
  intro T vT finT
  have nempty := validnonempty T vT
  have ffldnempty := (SP39 T vT).mpr nempty
  rcases ffldnempty with ⟨x, hx⟩
  have finffld := SP30 T finT
  have finpreds := SP38 T x hx finffld
  have first := SP36R T x
  have lor : (preds x T).Nonempty ∨ preds x T = ∅ := by
    exact Or.symm (Set.eq_empty_or_nonempty (preds x T))
  rcases lor with h1 | h2
  replace first := first h1 finpreds
  rcases first with ⟨z, hz1, hz2⟩
  have claim := (FL0 T z hz2).mpr hz1
  exact Exists.intro z claim
  have claim := (FL0 T x hx).mpr h2
  exact Exists.intro x claim

theorem FL4 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  valid_timeline τ → ∃ x, lasteles τ = {x} := by
  sorry

theorem FL5 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)) x,
  x ∈ firsteles τ → x ∈ ffld τ := by
  intro T x xin
  unfold firsteles at xin
  simp only [Set.mem_setOf_eq] at xin
  exact xin.1

theorem FL6 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)) x,
  x ∈ firsteles τ → ∀ y, y ∈ firsteles τ → x = y := by
  intro T x xinf y yinf
  have ffldx := FL5 T x xinf
  have vT : valid_timeline T := by
    unfold ffld order_set at ffldx
    simp only [Set.mem_setOf_eq] at ffldx
    exact ffldx.1
  have ffldy := FL5 T y yinf
  have fi := (FL0 T x (FL5 T x xinf)).mp xinf
  have fi2 := (FL0 T y (FL5 T y yinf)).mp yinf
  simp only [Set.empty_def, Set.ext_iff, Set.mem_setOf_eq] at fi fi2
  have toty := totality n T x y ⟨ffldx, ffldy, vT⟩
  rw [SP4RR T x y, SP4RR T y x] at toty
  rw [or_assoc.symm, or_right_comm, or_assoc, or_iff_not_imp_left] at toty
  have h := (fi y).mp
  simp only [imp_false] at h
  replace toty := toty h
  simp only [or_iff_not_imp_left] at toty
  replace h := (fi2 x).mp
  simp only [imp_false] at h
  exact toty h

theorem FL7 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  ((valid_timeline τ) → τ.Finite → ∃ x, firsteles τ  = {x}) := by
  intro T vT Tfin
  have exi := FL3 T vT Tfin
  rcases exi with ⟨x, xinf⟩
  have uni := FL6 T x xinf
  simp only [Set.ext_iff, Set.mem_singleton_iff, iff_def]
  have f : ∀ y, y = x → y ∈ firsteles T := by
      intro y yeq
      exact Set.mem_of_eq_of_mem yeq xinf
  use x
  intro y
  constructor
  · intro hy
    exact (uni y hy).symm
  · intro eqy
    exact f y eqy

theorem FL8 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  ((valid_timeline τ) → τ.Finite → ∃ x, lasteles τ  = {x}) := by
  sorry

theorem FL9 {κ : Type T} {n : ℕ} :
  ∀ (τ ρ : Set (timeline κ n × timeline κ n)),
  (valid_timeline ρ ∧ ρ ⊆ τ)
  → lasteles τ = lasteles ρ ∨ firsteles τ = firsteles ρ := by
  sorry





/-
!ADD# : Theorems regarding the addition of timelines via set unions
-/
theorem ADD0 {κ : Type T} {n : ℕ} :
  ∀ (τ ρ : Set (timeline κ n × timeline κ n)),
  ρ ⊆ τ → (subt τ ρ) ∪ ρ = τ := by
  intro T P subPT
  unfold subt
  ext x
  simp only [Set.mem_union, Set.mem_setOf_eq]
  simp only [Set.subset_def] at subPT
  constructor
  · intro hp1
    rcases hp1 with A | B
    exact A.1
    exact subPT x B
  · contrapose
    push Not
    intro hp2
    rcases hp2 with ⟨A, B⟩
    contrapose A
    push Not
    exact ⟨A, B⟩

theorem ADD1 {κ : Type T} {n : ℕ} :
  ∀ (τ ρ : Set (timeline κ n × timeline κ n)),
  (valid_timeline τ ∧ valid_timeline ρ ∧ lasteles τ = firsteles ρ)
  → ordered (τ ∪ ρ) := by
  sorry

theorem ADD2 {κ : Type T} {n : ℕ} :
  ∀ (τ ρ : Set (timeline κ n × timeline κ n)),
  (valid_timeline τ ∧ valid_timeline ρ ∧ lasteles τ = firsteles ρ)
  → nonbranching (τ ∪ ρ) := by
  sorry

theorem ADD3 {κ : Type T} {n : ℕ} :
  ∀ (τ ρ : Set (timeline κ n × timeline κ n)),
  (valid_timeline τ ∧ valid_timeline ρ ∧ lasteles τ = firsteles ρ)
  → strictly_ordered (τ ∪ ρ) := by
  sorry

theorem ADD4 {κ : Type T} {n : ℕ} :
  ∀ (τ ρ : Set (timeline κ n × timeline κ n)),
  (valid_timeline τ ∧ valid_timeline ρ ∧ lasteles τ = firsteles ρ)
  → (τ ∪ ρ).Nonempty := by
  sorry

theorem ADDN {κ : Type T} {n : ℕ} :
  ∀ (τ ρ : Set (timeline κ n × timeline κ n)),
  (valid_timeline τ ∧ valid_timeline ρ ∧ lasteles τ = firsteles ρ)
  → valid_timeline (τ ∪ ρ) := by
  sorry





/-
!SUBT# : Theorems regarding the substraction function
SUBT0 : Every timeline minus itself is equal to the empty set
SUBT1 : Every subtraction of timelines (T - P) is equal to the inverse
        timeline of (inverse T - inverse P)
SUBT2 : The first field of a timeline given by T - P, where T is a valid timeline and P is some
        timeline (valid or invalid), is a subset of the first field of T
SUBT3 : A timeline given by (T - P), the difference of two timelines T and P, is a subset of T
SUBT4 :
-/
theorem SUBT0 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  subt τ τ = ∅ := by
  intro T
  unfold subt
  rw [Set.ext_iff]
  intro x
  constructor
  · intro hp
    dsimp at hp
    rcases hp with ⟨h1, h2⟩
    have sthm1 : x ∈ T ∨ x ∈ {S | S ≠ S} := by
      left
      exact h1
    have sthm2 : x ∉ T → x ∈ {S | S ≠ S} := by
      intro hp
      cases sthm1 with
      | inl hp_true =>
        exact absurd hp_true hp
      | inr hq_true =>
        exact hq_true
    have sthm3 := sthm2 h2
    dsimp at sthm3
    simp only [Set.mem_empty_iff_false]
    have sthm4 : x ≠ x ↔ False := by
      tauto
    have sthm5 := sthm4.mp sthm3
    exact sthm5
  · intro hhp
    dsimp
    simp at hhp

theorem SUBT1 {κ : Type T} {n : ℕ} :
  ∀ (τ ρ : Set (timeline κ n × timeline κ n)),
  subt τ ρ = inv_timeline (subt (inv_timeline τ) (inv_timeline ρ)) := by
  intro T P
  --unfold subt
  rw [Set.ext_iff]
  intro x
  have sthm1 : ∀ τ, inv_pair x ∈ τ ↔ x ∈ inv_timeline τ := by
    intro R
    exact INV0 R (inv_pair x)
  have sthm2 := sthm1 (subt (inv_timeline T) (inv_timeline P))
  unfold subt at sthm2
  unfold subt
  constructor
  · intro h1
    dsimp at h1
    rw [sthm2.symm]
    simp only [Set.mem_setOf_eq]
    rcases h1 with ⟨shp1, shp2⟩
    constructor
    · have ssthm1 := sthm1 (inv_timeline T)
      have ssthm2 := F_INV0 T
      rw [ssthm2] at ssthm1
      exact ssthm1.mpr shp1
    · have ssthm1 := sthm1 (inv_timeline P)
      have ssthm2 := F_INV0 P
      rw [ssthm2] at ssthm1
      have ssthm3 : inv_pair x ∉ inv_timeline P ↔ x ∉ P := by
        exact not_iff_not.mpr ssthm1
      exact ssthm3.mpr shp2
  · intro h2
    have sthm1 : ∀ τ, inv_pair x ∈ τ ↔ x ∈ inv_timeline τ := by
      intro R
      exact INV0 R (inv_pair x)
    have sthm2 := sthm1 (subt (inv_timeline T) (inv_timeline P))
    unfold subt at sthm2
    rw [sthm2.symm] at h2
    dsimp at h2
    dsimp
    rcases h2 with ⟨shp1, shp2⟩
    have sthm3 := sthm1 (inv_timeline T)
    have sthm4 := F_INV0 T
    rw [sthm4] at sthm3
    have sthm5 := sthm1 (inv_timeline P)
    have sthm6 := F_INV0 P
    rw [sthm6] at sthm5
    have sthm7 : inv_pair x ∉ inv_timeline P ↔ x ∉ P := by
        exact not_iff_not.mpr sthm5
    constructor
    · exact sthm3.mp shp1
    · exact sthm7.mp shp2

theorem SUBT2 {κ : Type T} {n : ℕ} :
  ∀ (τ ρ : Set (timeline κ n × timeline κ n)),
  valid_timeline τ
  → ffld (subt τ ρ) ⊆ ffld τ := by
  intro T P hT
  unfold ffld
  unfold subt
  dsimp only [Set.mem_setOf_eq]
  simp only [Prod.exists, Set.setOf_subset_setOf, and_imp, forall_exists_index]
  intro A hp1 x y hp2 hp3 hp4
  constructor
  · unfold order_set
    dsimp only [Set.mem_setOf_eq]
    exact hT
  · have sthm1 : (x, y) ∈ T ∧ (x = A ∨ y = A) := by
      constructor
      · exact hp2
      · exact hp4
    exact ⟨x, y, sthm1⟩

theorem SUBT3 {κ : Type T} {n : ℕ} :
  ∀ (τ ρ : Set (timeline κ n × timeline κ n)),
  subt τ ρ ⊆ τ := by
  simp only [Set.subset_def]
  intro T P x
  unfold subt
  simp only [Set.mem_setOf_eq]
  intro hx
  exact hx.1

theorem SUBT4 {κ : Type T} {n : ℕ} :
  ∀ (τ ρ : Set (timeline κ n × timeline κ n)),
  (valid_timeline τ ∧ valid_timeline ρ ∧ valid_timeline (subt τ ρ) ∧ ρ ⊆ τ) →
  ∀ x ∈ ffld ρ, ∀ y ∈ ffld (subt τ ρ), y ∈ (succs x τ) ∨ y ∈ (preds x τ) ∨ y = x := by
  intro T P h x fx y fsy
  rcases h with ⟨vT, vP, vSubt, subPT⟩
  have ffld_subTP := FLD0 T P ⟨vT, vP, subPT⟩
  have ffld_sub := SUBT2 T P vT
  simp only [Set.subset_def] at subPT ffld_sub ffld_subTP
  specialize ffld_sub y fsy
  have x_in_T := ffld_subTP x fx
  simp only [Prod.forall] at subPT
  unfold preds
  simp only [Set.mem_setOf_eq]
  rw [or_iff_not_imp_left]
  intro hp1
  rw [or_iff_not_imp_left]
  contrapose
  intro hp2
  simp only [ne_eq]
  refine ⟨ffld_sub, x_in_T, ?_, hp2⟩
  exact hp1

theorem SUBT5 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  ordered τ →
  ∀ (ρ : Set (timeline κ n × timeline κ n)),
  (ρ ⊆ τ ∧ ordered ρ ∧ ρ ≠ τ) → ordered (subt τ ρ) := by
  sorry

theorem SUBT6 {κ : Type T} {n : ℕ} :
  ∀ (τ ρ : Set (timeline κ n × timeline κ n)),
  subt τ ρ ∩ ρ = ∅ := by
  intro T P
  unfold subt
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and,
    and_imp, imp_self, implies_true]

theorem SUBT7 {κ : Type T} {n : ℕ} :
  ∀ (τ ρ : Set (timeline κ n × timeline κ n)),
  (valid_timeline τ ∧ valid_timeline ρ ∧ valid_timeline (subt τ ρ) ∧ ¬ single τ ∧ ρ ⊆ τ)
  → ∃! x, x ∈ ffld (subt τ ρ) ∩ ffld ρ := by
  intro T P
  intro ⟨⟨nbT, orderT, sorderT, nemptyT⟩, ⟨nbP, orderP, sorderP, nemptyP⟩, ⟨nbS, orderS, sorderS, nemptyS⟩, nsing, subPT⟩
  unfold nonbranching at nbT nbP nbS
  unfold ordered at orderT orderP orderS
  simp [or_iff_not_imp_left] at orderT
  replace orderT := orderT nsing nemptyT
  rcases nemptyP with ⟨x, xinP⟩
  rcases nemptyS with ⟨y, yinS⟩
  have yinT := SUBT3 T P yinS
  have xinT := subPT xinP
  have orderTx := orderT x.1 x.2 xinT
  have exclus := SUBT6 T P
  have comp := ADD0 T P subPT
  simp only [Set.ext_iff, Set.mem_inter_iff, Set.mem_union] at exclus comp
  have exclusy := (exclus y).mp
  have compy := comp y
  simp only [Set.mem_empty_iff_false, imp_false, not_and] at exclusy
  replace exclusy := exclusy yinS
  unfold ffld order_set
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  have orderTy := orderT y.1 y.2 yinT
  let last := lasteles P
  let first := firsteles T
  sorry


theorem SUBT8 {κ : Type T} {n : ℕ} :
  ∀ (τ ρ : Set (timeline κ n × timeline κ n)),
  (valid_timeline τ ∧ valid_timeline ρ ∧ ρ ⊆ τ) →
  (∃ (p : timeline κ n × timeline κ n), p ∈ ρ ∧ succs p.1 τ = ∅)
  → ∀ x ∈ ffld ρ, ∀ y ∈ ffld (subt τ ρ), x ≠ y → y ∈ preds x τ := by
  intro T P
  simp only [and_imp]
  intro vT vP subPT exi_p x ffldx y ffldy xney
  have ffld_subPT := FLD0 T P ⟨vT, vP, subPT⟩
  have ffld_subtTP := SUBT2 T P vT
  rcases exi_p with ⟨p, pinP, empt⟩
  simp only [Set.subset_def] at subPT ffld_subPT ffld_subtTP
  specialize ffld_subtTP y ffldy
  have ffldxT := ffld_subPT x ffldx
  have pinT := subPT p pinP
  --have xsucc := SP6 T p.1 empt x ffldxT
  --have ysucc := SP6 T p.1 empt y ffld_subtTP
  have tot := totality n T x y ⟨ffldxT, ffld_subtTP, vT⟩
  simp only [xney, false_or] at tot
  have temp := SP4 T y x vT
  rw [temp] at tot
  have PTexclusive := SUBT6 T P
  have contra : y ∈ succs x T → False := by
    intro ysuccx
    sorry
  sorry





/-
!COUNT# : Theorems regarding the cardinality of timelines and of fields
-/
/-theorem COUNT0 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  τ-/

theorem COUNTN {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  valid_timeline τ → (∃ m > 0, m = τ.ncard) → (ffld τ).ncard = τ.ncard + 1 := by
  intro T vT ⟨m, mgz, hm⟩
  induction m generalizing T with
  | zero =>
    omega
  | succ m ih =>
    cases m with
    | zero =>
      have hme := hm.symm
      simp only [zero_add, Set.ncard_eq_one, Prod.exists] at hme
      rw [hm.symm]
      simp only [Nat.reduceAdd]
      rcases hme with ⟨a, b, hp⟩
      unfold ffld
      have claim := SP9 T vT
      simp only [Prod.forall] at claim
      have belT : (a, b) ∈ T := by
        rw [hp]
        rfl
      replace claim := claim a b belT
      have acard : ({a} : Set (timeline κ n)).ncard = 1 := Set.ncard_singleton a
      have bcard : ({b} : Set (timeline κ n)).ncard = 1 := Set.ncard_singleton b
      have aneb : ({a} : Set (timeline κ n)) ∩ ({b} : Set (timeline κ n)) = ∅ := by
        simp only [Set.empty_def, Set.ext_iff, Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
        intro x
        constructor
        · intro h1
          rw [h1.1] at h1
          exact claim h1.2
        · intro h2
          contradiction
      have adisjb : Disjoint ({a} : Set (timeline κ n)) ({b} : Set (timeline κ n))
        := Set.disjoint_iff_inter_eq_empty.mpr aneb
      have cardab : (({a} : Set (timeline κ n)) ∪ ({b} : Set (timeline κ n))).ncard = 2 := by
        rw [Set.ncard_union_eq adisjb, acard, bcard]
      have sset : ffld T = {a} ∪ {b} := by
        unfold ffld order_set
        simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
        intro x
        constructor
        · intro hp1
          rcases hp1.2 with ⟨q, qinT, hq⟩
          rw [hp] at qinT
          simp only [Set.mem_singleton_iff,  Prod.eq_iff_fst_eq_snd_eq] at qinT
          rw [qinT.1, qinT.2] at hq
          rcases hq with hq1 | hq2
          left
          exact hq1.symm
          right
          exact hq2.symm
        · intro hp2
          refine ⟨vT, ?_⟩
          simp only [Prod.exists]
          refine ⟨a, b, belT, ?_⟩
          rcases hp2 with hp21 | hp22
          left
          exact hp21.symm
          right
          exact hp22.symm
      rw [sset.symm] at cardab
      unfold ffld at cardab
      exact cardab
    | succ k =>
      sorry


/-
!DIST# : Theorems regarding the distance function
DIST0 - The distance between A and A in a timeline T is 0
DIST1 - The distance function is perfectly symmetric
DIST2 - The distance between A and B in T is the same as in inv_timeline T
-/
theorem DIST0 {κ : Type T} (k n : ℕ) (A : timeline κ (k + n)) :
  ∀ (τ : Set (timeline κ (k + n) × timeline κ (k + n))),
  tdist k n A A τ = 0 := by
  unfold tdist
  intro T
  unfold fld
  sorry

theorem DIST1 {κ : Type T} (k n : ℕ) (A B : timeline κ (k + n)) :
  ∀ (τ : Set (timeline κ (k + n) × timeline κ (k + n))),
  tdist k n B A τ = tdist k n A B τ := by
  sorry
