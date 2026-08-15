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

theorem SP5 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (A B : timeline κ n),
  valid_timeline τ → (B ∈ succs A τ ↔ B ∈ preds A (inv_timeline τ)) := by
  sorry

theorem SP6 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (B : timeline κ n),
  (succs B τ) = ∅ → ∀ A ∈ ffld τ, A ∈ preds B τ := by
  sorry

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
  valid_timeline τ → (∀ x y, x ∈ succs y τ → (succs x τ ⊂ succs y τ)) := by
  intro T vT x y xinP
  --rw [SP4 T y x vT] at xinP
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
  valid_timeline τ → ∀ (A B : timeline κ n),
  A ∈ succs B τ → succs A τ ⊆ succs B τ := by
    intro T vT A B hA
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
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  (valid_timeline τ ∧ (ffld τ).Finite) → (∀ x y, is_imm_succ y x τ → (succs y τ).ncard + 1 = (succs x τ).ncard) := by
  intro T ⟨vT, finfld⟩ x y ysx
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = (succs x T).ncard := by
    exact ⟨(succs x T).ncard, rfl⟩
  have yssx := SP0 T x y ysx
  have claim := SP14 T vT y x yssx
  have extclaim := SP16 T vT y x yssx
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
    · intro eqq
      rw [eqq]
      exact irreflexy


theorem SP19 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  valid_timeline τ → (∀ x, (preds x τ).Finite → ∃ z, preds z τ = ∅) := by
  intro T vT x finpreds
  have subsetcl := fun (y : timeline κ n) => SP13 T vT y x
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = (preds x T).ncard := by
    exact ⟨(preds x T).ncard, rfl⟩
  induction n with
  | zero =>


theorem SPINFINITY {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  (valid_timeline τ ∧ (∀ x ∈ ffld τ, ∃ y, y ∈ preds x τ)) → ¬ (τ.Finite) := by
  unfold ffld order_set
  intro T ⟨⟨nbT, orderT, sorderT, nemptyT⟩, all⟩
  --unfold preds at all
  simp only [Set.mem_setOf_eq, and_imp] at all
  have transit := transitivity n T
  have irreflex := irreflexivity n T
  have infin := SP12 T ⟨nbT, orderT, sorderT, nemptyT⟩
  have infins := SP13 T ⟨nbT, orderT, sorderT, nemptyT⟩
  replace all := (fun (vT : valid_timeline T) (x : timeline κ n) => all x vT) ⟨nbT, orderT, sorderT, nemptyT⟩
  have claim : ∀ x ∈ ffld T, (preds x T).Nonempty := by
    intro x xinffld
    unfold ffld at xinffld
    simp only [Set.mem_setOf_eq] at xinffld
    have nclaim := all x xinffld.2
    exact nclaim
  intro hfin
  have hffld : (ffld T).Finite := by
    have hfst : (Prod.fst '' T).Finite := hfin.image Prod.fst
    have hsnd : (Prod.snd '' T).Finite := hfin.image Prod.snd
    apply (hfst.union hsnd).subset
    intro x hx
    rcases hx with ⟨_, p, hpT, hpx | hpx⟩
    · left
      exact ⟨p, hpT, hpx⟩
    · right
      exact ⟨p, hpT, hpx⟩
  have hpreds : ∀ x ∈ ffld T, (preds x T).Finite := by
    intro x hx
    apply hffld.subset
    intro y hy
    unfold preds at hy
    simp only [Set.mem_setOf_eq] at hy
    exact hy.1

  --simp only [ne_eq, Set.sep_and, Set.mem_inter_iff] at all




/-
!FL# : Theorems regarding the the definition of lasteles and firsteles
-/
/-theorem FL0 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  τ.Finite → ∃ x-/

theorem FL1 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  ¬ single τ →
  ((valid_timeline τ) → (τ.Finite → ∃ x, firsteles τ = {x})) := by
  intro T nsing ⟨nbT, orderT, sorderT, nemptyT⟩ finite
  unfold firsteles
  have val : valid_timeline T := ⟨nbT, orderT, sorderT, nemptyT⟩
  have fnbT := fundnonbranching T nbT
  rcases nemptyT with ⟨y, yinT⟩
  unfold ordered at orderT
  --have orderTN := orderT
  unfold nonbranching at nbT
  unfold strictly_ordered at sorderT
  simp [or_iff_not_imp_left] at orderT
  have orderTN := orderT nsing ⟨y, yinT⟩ y.1 y.2 yinT
  replace orderT := orderT nsing ⟨y, yinT⟩
  let S := {s | s ∈ ffld T ∧ ∀ p ∈ T, p.2 ≠ s}
  have eq : S = {s | s ∈ ffld T ∧ ∀ p ∈ T, p.2 ≠ s} := rfl
  have exten : y.1 ∈ S ↔ y.1 ∈ ffld T ∧ ∀ p ∈ T, p.2 ≠ y.1 := by
    rw [eq]
    simp only [Set.mem_setOf_eq]
  have ffldy : y.1 ∈ ffld T := by
    unfold ffld order_set
    simp only [Set.mem_setOf_eq]
    refine ⟨val, ?_⟩
    have lor : y.1 = y.1 ∨ y.2 = y.1 := by
      left
      rfl
    exact ⟨y, yinT, lor⟩
  have new := exten.mpr
  simp only [and_imp] at new
  replace new := new ffldy
  rw [eq.symm]
  have contra : ¬ (∃ x ∈ T, ∀ p ∈ T, p.2 ≠ x.1) → False := by
    push Not
    intro contrahp
    simp only [Prod.exists, exists_eq_right, Prod.forall] at contrahp
  have hpnew : ∃ x ∈ T, ∀ p ∈ T, p.2 ≠ x.1 := by


theorem FL2 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  valid_timeline τ → ∃ x, lasteles τ = {x} := by

theorem FL3 {κ : Type T} {n : ℕ} :
  ∀ (τ ρ : Set (timeline κ n × timeline κ n)),
  (valid_timeline ρ ∧ ρ ⊆ τ)
  → lasteles τ = lasteles ρ ∨ firsteles τ = firsteles ρ := by





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
  have xsucc := SP6 T p.1 empt x ffldxT
  have ysucc := SP6 T p.1 empt y ffld_subtTP
  have tot := totality n T x y ⟨ffldxT, ffld_subtTP, vT⟩
  simp only [xney, false_or] at tot
  have temp := SP4 T y x vT
  rw [temp] at tot
  have PTexclusive := SUBT6 T P
  have contra : y ∈ succs x T → False := by
    intro ysuccx





/-
!COUNT# : Theorems regarding the cardinality of timelines and of fields
-/
theorem COUNT0 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  τ

theorem COUNTN {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  valid_timeline τ → (ffld τ).ncard = 1 + τ.ncard := by



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
