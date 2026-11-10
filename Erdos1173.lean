/-
Private formalization of the negative answer to Erdos problem 1173.
Do not publish or submit without the owner's explicit authorization.

The definition of Cardinal.GCH below is copied from
google-deepmind/formal-conjectures, ContinuumHypothesis.lean (Apache-2.0),
blob 2dc4ec4a8da10e05826166610abdb06faa1f4f25.
-/
import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

set_option autoImplicit false

open Cardinal Ordinal Set Function
open scoped Cardinal Ordinal
noncomputable section

namespace Cardinal
def GCH : Prop :=
  ∀ o : Ordinal.{0}, (2 : Cardinal.{0}) ^ ℵ_ o = ℵ_ (Order.succ o)
end Cardinal

namespace Erdos1173

abbrev mu : Cardinal.{0} := ℵ_ ω
abbrev kappa : Cardinal.{0} := ℵ_ (ω + 1)
abbrev M := Σ n : ℕ, (ℵ_ (n : Ordinal.{0})).out
abbrev X := ℕ → M
abbrev Code := Σ n : ℕ, Fin n → M

theorem mu_infinite : ℵ₀ ≤ mu := aleph0_le_aleph _

theorem mu_lt_kappa : mu < kappa :=
  aleph_lt_aleph.mpr (lt_add_one _)

theorem aleph_nat_lt_mu (n : ℕ) : ℵ_ (n : Ordinal.{0}) < mu :=
  aleph_lt_aleph.mpr (natCast_lt_omega0 n)

theorem aleph_nat_sup : (⨆ n : ℕ, ℵ_ (n : Ordinal.{0})) = mu := by
  apply le_antisymm
  · exact ciSup_le' fun n => (aleph_nat_lt_mu n).le
  · change ℵ_ ω ≤ _
    rw [aleph_limit isSuccLimit_omega0]
    apply ciSup_le'
    intro a
    obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp a.property
    rw [hn]
    exact le_ciSup (show BddAbove (Set.range (fun n : ℕ => ℵ_ (n : Ordinal.{0}))) from
      ⟨mu, by rintro c ⟨n, rfl⟩; exact (aleph_nat_lt_mu n).le⟩) n

theorem mk_M : #M = mu := by
  rw [mk_sigma]
  simp only [mk_out]
  apply le_antisymm
  · calc
      Cardinal.sum (fun n : ℕ => ℵ_ (n : Ordinal.{0}))
          ≤ #ℕ * ⨆ n : ℕ, ℵ_ (n : Ordinal.{0}) := sum_le_mk_mul_iSup _
      _ = mu := by rw [mk_nat, aleph_nat_sup, mul_eq_right mu_infinite mu_infinite aleph0_ne_zero]
  · rw [← aleph_nat_sup]
    exact iSup_le_sum _

theorem mu_cof : mu.ord.cof = ℵ₀ := by
  rw [ord_aleph, cof_omega isSuccLimit_omega0, Ordinal.cof_omega0]

theorem mk_X (h : Cardinal.GCH) : #X = kappa := by
  have hpow : (2 : Cardinal.{0}) ^ mu = kappa := by
    simpa only [Order.succ_eq_add_one] using h ω
  have hlo : mu < mu ^ ℵ₀ := by
    simpa only [mu_cof] using lt_power_cof_ord mu_infinite
  rw [mk_arrow, Cardinal.lift_id, Cardinal.lift_id, mk_nat, mk_M]
  apply le_antisymm
  · calc
      mu ^ ℵ₀ ≤ mu ^ mu := power_le_power_left (ne_of_gt (aleph_pos _)) mu_infinite
      _ = (2 : Cardinal) ^ mu := power_self_eq mu_infinite
      _ = kappa := hpow
  · simpa only [mu, kappa, succ_aleph] using
      (Order.succ_le_iff.mpr hlo : Order.succ mu ≤ mu ^ ℵ₀)

theorem mk_low (N : ℕ) : #({m : M | m.1 < N} : Set M) ≤ ℵ_ (N : Ordinal.{0}) := by
  let e : {m : M // m.1 < N} ↪ (Σ n : Fin N, (ℵ_ (n : Ordinal.{0})).out) :=
    { toFun := fun m => ⟨⟨m.val.1, m.property⟩, m.val.2⟩
      inj' := by
        intro a b hab
        apply Subtype.ext
        have h := congrArg (fun x : Σ n : Fin N, (ℵ_ (n : Ordinal.{0})).out =>
          (⟨x.1.val, x.2⟩ : M)) hab
        exact h }
  calc
    #({m : M | m.1 < N} : Set M) ≤ #(Σ n : Fin N, (ℵ_ (n : Ordinal.{0})).out) :=
      mk_le_of_injective e.injective
    _ = Cardinal.sum (fun n : Fin N => ℵ_ (n : Ordinal.{0})) := by simp only [mk_sigma, mk_out]
    _ ≤ Cardinal.sum (fun _ : Fin N => ℵ_ (N : Ordinal.{0})) :=
      sum_le_sum _ _ fun n => aleph_le_aleph.mpr (by exact_mod_cast n.isLt.le)
    _ = #(Fin N) * ℵ_ (N : Ordinal.{0}) := sum_const' _ _
    _ ≤ ℵ_ (N : Ordinal.{0}) * ℵ_ (N : Ordinal.{0}) := by
      apply mul_le_mul_left
      exact (show #(Fin N) ≤ ℵ₀ by simp only [mk_fin, natCast_le_aleph0]).trans (aleph0_le_aleph _)
    _ = ℵ_ (N : Ordinal.{0}) := mul_eq_self (aleph0_le_aleph _)

theorem mk_Code : #Code ≤ mu := by
  rw [mk_sigma]
  calc
    Cardinal.sum (fun n : ℕ => #(Fin n → M)) ≤ Cardinal.sum (fun _ : ℕ => mu) := by
      apply sum_le_sum
      intro n
      simpa only [mk_arrow, Cardinal.lift_id, mk_fin, mk_M, power_natCast] using power_nat_le (c := mu) (n := n) mu_infinite
    _ = #ℕ * mu := sum_const' _ _
    _ = mu := by rw [mk_nat, mul_eq_right mu_infinite mu_infinite aleph0_ne_zero]

abbrev Family := {A : Set X // #A = mu}

def familyListing (A : Family) : M → X :=
  fun m => (Classical.choice (Cardinal.eq.mp (mk_M.trans A.property.symm)) m).val

theorem range_familyListing (A : Family) : Set.range (familyListing A) = A.val := by
  let e : M ≃ A.val := Classical.choice (Cardinal.eq.mp (mk_M.trans A.property.symm))
  ext x
  constructor
  · rintro ⟨m, rfl⟩
    exact (e m).property
  · intro hx
    exact ⟨e.symm ⟨x, hx⟩, by simp [familyListing, e]⟩

theorem familyListing_injective : Function.Injective familyListing := by
  intro A B h
  apply Subtype.ext
  rw [← range_familyListing A, ← range_familyListing B, h]

theorem mk_Family (h : Cardinal.GCH) : #Family ≤ kappa := by
  calc
    #Family ≤ #(M → X) := mk_le_of_injective familyListing_injective
    _ = kappa ^ mu := by simp only [mk_arrow, Cardinal.lift_id, mk_M, mk_X h]
    _ = kappa := by
      have hpow : (2 : Cardinal.{0}) ^ mu = kappa := by
        simpa only [Order.succ_eq_add_one] using h ω
      rw [← hpow, ← power_mul, mul_eq_self mu_infinite]

theorem small_of_lt_kappa {c : Cardinal.{0}} (hc : c < kappa) : c ≤ mu := by
  change c < ℵ_ (ω + 1) at hc
  rw [← succ_aleph] at hc
  exact Order.lt_succ_iff.mp hc

abbrev Index := kappa.ord.ToType

def pointIndex (h : Cardinal.GCH) : X ≃ Index :=
  Classical.choice (Cardinal.eq.mp ((mk_X h).trans (mk_ord_toType kappa).symm))

def familyIndex (h : Cardinal.GCH) : Family ↪ Index :=
  Classical.choice ((Cardinal.le_def Family Index).mp (by simpa using mk_Family h))

theorem initial_small (i : Index) : #(Set.Iio i) ≤ mu := by
  apply small_of_lt_kappa
  simpa using mk_Iio_lt i (by simp)

theorem initial_closed_small (i : Index) : #(Set.Iic i) ≤ mu := by
  apply small_of_lt_kappa
  simpa using mk_Iic_lt i (by simp) (by simp)

def initialSegment (n : ℕ) (x : X) : Fin n → M := fun i => x i

theorem prefix_mono {m n : ℕ} (hmn : m ≤ n) {x y : X}
    (hxy : initialSegment n x = initialSegment n y) : initialSegment m x = initialSegment m y := by
  funext i
  exact congrFun hxy (⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ : Fin n)

theorem distinct_prefix {x y : X} (hxy : x ≠ y) : ∃ n, initialSegment n x ≠ initialSegment n y := by
  classical
  have hi : ∃ i, x i ≠ y i := by
    by_contra hn
    apply hxy
    funext i
    exact not_not.mp (fun h => hn ⟨i, h⟩)
  obtain ⟨i, hi⟩ := hi
  refine ⟨i + 1, fun h => hi ?_⟩
  exact congrFun h (⟨i, Nat.lt_succ_self i⟩ : Fin (i + 1))

def Accumulates (A : Set X) (x : X) : Prop :=
  ∀ n, ∃ y ∈ A, y ≠ x ∧ initialSegment n x = initialSegment n y

abbrev Requests (h : Cardinal.GCH) (x : X) :=
  {A : Family // familyIndex h A < pointIndex h x ∧ Accumulates A.val x}

theorem requests_small (h : Cardinal.GCH) (x : X) : #(Requests h x) ≤ mu := by
  let e : Requests h x ↪ Set.Iio (pointIndex h x) :=
    { toFun := fun A => ⟨familyIndex h A.val, A.property.1⟩
      inj' := by
        intro A B he
        apply Subtype.ext
        exact (familyIndex h).injective (congrArg Subtype.val he) }
  exact (mk_le_of_injective e.injective).trans (initial_small _)

def encode (h : Cardinal.GCH) (x : X) : Requests h x ↪ M :=
  Classical.choice ((Cardinal.le_def (Requests h x) M).mp (by
    rw [mk_M]
    exact requests_small h x))

def chosen (h : Cardinal.GCH) (x : X) (r : Requests h x) : X :=
  Classical.choose (r.property.2 ((encode h x r).1))

theorem chosen_spec (h : Cardinal.GCH) (x : X) (r : Requests h x) :
    chosen h x r ∈ r.val.val ∧ chosen h x r ≠ x ∧
      initialSegment (encode h x r).1 x = initialSegment (encode h x r).1 (chosen h x r) :=
  Classical.choose_spec (r.property.2 ((encode h x r).1))

def mapping (h : Cardinal.GCH) (x : X) : Set X := Set.range (chosen h x)

theorem mapping_avoids_self (h : Cardinal.GCH) (x : X) : x ∉ mapping h x := by
  rintro ⟨r, hr⟩
  exact (chosen_spec h x r).2.1 hr

theorem mapping_small (h : Cardinal.GCH) (x : X) : #(mapping h x) ≤ mu :=
  mk_range_le.trans (requests_small h x)

theorem mapping_exceptions (h : Cardinal.GCH) (x : X) (N : ℕ) :
    #({y ∈ mapping h x | initialSegment N x ≠ initialSegment N y} : Set X) ≤ ℵ_ (N : Ordinal.{0}) := by
  let early : Set (Requests h x) := {r | (encode h x r).1 < N}
  have hearly : #early ≤ ℵ_ (N : Ordinal.{0}) := by
    let e : early ↪ {m : M // m.1 < N} :=
      { toFun := fun r => ⟨encode h x r.val, r.property⟩
        inj' := by
          intro a b hab
          apply Subtype.ext
          exact (encode h x).injective (congrArg Subtype.val hab) }
    exact (mk_le_of_injective e.injective).trans (mk_low N)
  have hsub : {y ∈ mapping h x | initialSegment N x ≠ initialSegment N y} ⊆ chosen h x '' early := by
    rintro y ⟨⟨r, rfl⟩, hne⟩
    refine ⟨r, ?_, rfl⟩
    change (encode h x r).1 < N
    by_contra hn
    exact hne (prefix_mono (Nat.le_of_not_gt hn) (chosen_spec h x r).2.2)
  exact (mk_le_mk_of_subset hsub).trans (mk_image_le.trans hearly)

theorem mapping_intersection (h : Cardinal.GCH) {x y : X} (hxy : x ≠ y) :
    #(mapping h x ∩ mapping h y : Set X) < mu := by
  obtain ⟨N, hN⟩ := distinct_prefix hxy
  let E (z : X) : Set X := {v ∈ mapping h z | initialSegment N z ≠ initialSegment N v}
  have hsub : mapping h x ∩ mapping h y ⊆ E x ∪ E y := by
    rintro v ⟨hx, hy⟩
    by_cases hpx : initialSegment N x = initialSegment N v
    · exact Or.inr ⟨hy, fun hpy => hN (hpx.trans hpy.symm)⟩
    · exact Or.inl ⟨hx, hpx⟩
  calc
    #(mapping h x ∩ mapping h y : Set X) ≤ #(E x ∪ E y : Set X) := mk_le_mk_of_subset hsub
    _ ≤ #(E x) + #(E y) := mk_union_le _ _
    _ ≤ ℵ_ (N : Ordinal.{0}) + ℵ_ (N : Ordinal.{0}) :=
      add_le_add (mapping_exceptions h x N) (mapping_exceptions h y N)
    _ = ℵ_ (N : Ordinal.{0}) := add_eq_self (aleph0_le_aleph _)
    _ < mu := aleph_nat_lt_mu N

theorem small_dense_subset (H : Set X) :
    ∃ D : Set X, D ⊆ H ∧ #D ≤ mu ∧
      ∀ x ∈ H, ∀ n, ∃ y ∈ D, initialSegment n x = initialSegment n y := by
  classical
  let Used := {c : Code // ∃ y ∈ H, initialSegment c.1 y = c.2}
  let pick (c : Used) : X := Classical.choose c.property
  have hpick (c : Used) : pick c ∈ H ∧ initialSegment c.val.1 (pick c) = c.val.2 :=
    Classical.choose_spec c.property
  refine ⟨Set.range pick, ?_, ?_, ?_⟩
  · rintro y ⟨c, rfl⟩
    exact (hpick c).1
  · exact mk_range_le.trans ((mk_subtype_le _).trans mk_Code)
  · intro x hx n
    let c : Used := ⟨⟨n, initialSegment n x⟩, x, hx, rfl⟩
    exact ⟨pick c, ⟨c, rfl⟩, (hpick c).2.symm⟩

theorem dense_family (H : Set X) (hH : #H = kappa) :
    ∃ A : Family, A.val ⊆ H ∧
      ∀ x ∈ H, ∀ n, ∃ y ∈ A.val, initialSegment n x = initialSegment n y := by
  obtain ⟨D, hDH, hD, hdense⟩ := small_dense_subset H
  obtain ⟨B, hBH, hB⟩ := (le_mk_iff_exists_subset).mp (show mu ≤ #H by rw [hH]; exact mu_lt_kappa.le)
  have hDB : #(D ∪ B : Set X) = mu := by
    apply le_antisymm
    · exact (mk_union_le D B).trans (by simpa only [hB, add_eq_self mu_infinite] using add_le_add hD (le_refl mu))
    · rw [← hB]
      exact mk_le_mk_of_subset (Set.subset_union_right)
  refine ⟨⟨D ∪ B, hDB⟩, Set.union_subset hDH hBH, ?_⟩
  intro x hx n
  obtain ⟨y, hy, he⟩ := hdense x hx n
  exact ⟨y, Or.inl hy, he⟩

theorem large_set_has_edge (h : Cardinal.GCH) (H : Set X) (hH : #H = kappa) :
    ∃ x ∈ H, ∃ y ∈ H, x ≠ y ∧ y ∈ mapping h x := by
  classical
  obtain ⟨A, hAH, hdense⟩ := dense_family H hH
  let T : Set X := (pointIndex h) ⁻¹' Set.Iic (familyIndex h A)
  have hT : #T ≤ mu := by
    rw [show #T = #(Set.Iic (familyIndex h A)) from mk_preimage_equiv _ _]
    exact initial_closed_small _
  have hgood : ∃ x ∈ H, x ∉ A.val ∧ familyIndex h A < pointIndex h x := by
    by_contra hn
    have hsub : H ⊆ A.val ∪ T := by
      intro x hx
      by_cases hxa : x ∈ A.val
      · exact Or.inl hxa
      · right
        change pointIndex h x ≤ familyIndex h A
        exact le_of_not_gt (fun hlt => hn ⟨x, hx, hxa, hlt⟩)
    have hh : #H ≤ mu := calc
      #H ≤ #(A.val ∪ T : Set X) := mk_le_mk_of_subset hsub
      _ ≤ #A.val + #T := mk_union_le _ _
      _ ≤ mu + mu := add_le_add A.property.le hT
      _ = mu := add_eq_self mu_infinite
    exact (not_le_of_gt mu_lt_kappa) (hH ▸ hh)
  obtain ⟨x, hxH, hxA, hlate⟩ := hgood
  have hacc : Accumulates A.val x := by
    intro n
    obtain ⟨y, hyA, he⟩ := hdense x hxH n
    exact ⟨y, hyA, (fun hxy => hxA (hxy ▸ hyA)), he⟩
  let r : Requests h x := ⟨A, hlate, hacc⟩
  refine ⟨x, hxH, chosen h x r, hAH (chosen_spec h x r).1,
    (chosen_spec h x r).2.1.symm, ?_⟩
  exact ⟨r, rfl⟩

/- The following two definitions reproduce the formal-conjectures statement. -/
abbrev Domain : Type := (ω_ (ω + 1 : Ordinal.{0})).ToType

def IsSetMapping (f : Domain → Set Domain) : Prop :=
  (∀ α, α ∉ f α) ∧
  (∀ α, #(f α) ≤ ℵ_ ω) ∧
  (∀ α β, α ≠ β → #(f α ∩ f β : Set Domain) < ℵ_ ω)

def IsFreeSet (f : Domain → Set Domain) (Y : Set Domain) : Prop :=
  ∀ α ∈ Y, ∀ β ∈ Y, α ≠ β → β ∉ f α

theorem mk_Domain : #Domain = kappa := by simp [Domain, kappa]

def domainEquiv (h : Cardinal.GCH) : Domain ≃ X :=
  Classical.choice (Cardinal.eq.mp (mk_Domain.trans (mk_X h).symm))

def counterexample (h : Cardinal.GCH) (a : Domain) : Set Domain :=
  (domainEquiv h) ⁻¹' mapping h (domainEquiv h a)

theorem counterexample_isSetMapping (h : Cardinal.GCH) : IsSetMapping (counterexample h) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact mapping_avoids_self h (domainEquiv h a)
  · intro a
    change #((domainEquiv h) ⁻¹' mapping h (domainEquiv h a)) ≤ mu
    rw [mk_preimage_equiv]
    exact mapping_small h _
  · intro a b hab
    change #((domainEquiv h) ⁻¹' mapping h (domainEquiv h a) ∩
      (domainEquiv h) ⁻¹' mapping h (domainEquiv h b) : Set Domain) < mu
    rw [← Set.preimage_inter, mk_preimage_equiv]
    exact mapping_intersection h (fun he => hab ((domainEquiv h).injective he))

theorem counterexample_no_large_free_set (h : Cardinal.GCH) (Y : Set Domain)
    (hfree : IsFreeSet (counterexample h) Y) : #Y ≠ kappa := by
  intro hY
  have hH : #((domainEquiv h) '' Y) = kappa := by
    rw [mk_image_eq (domainEquiv h).injective, hY]
  obtain ⟨x, hx, y, hy, hxy, hedge⟩ := large_set_has_edge h _ hH
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact hfree a ha b hb (fun he => hxy (congrArg (domainEquiv h) he)) hedge

/-- Under GCH the conditions in Erdős 1173 admit a counterexample. -/
theorem erdos_1173_counterexample : Cardinal.GCH →
    ∃ f : Domain → Set Domain, IsSetMapping f ∧
      ∀ Y : Set Domain, IsFreeSet f Y → #Y ≠ ℵ_ (ω + 1) := by
  intro h
  exact ⟨counterexample h, counterexample_isSetMapping h, counterexample_no_large_free_set h⟩

/-- The precise negation of the proposed positive conclusion, conditional on GCH. -/
theorem erdos_1173_negative : Cardinal.GCH →
    ¬ (∀ f : Domain → Set Domain, IsSetMapping f →
      ∃ Y : Set Domain, IsFreeSet f Y ∧ #Y = ℵ_ (ω + 1)) := by
  intro h hp
  obtain ⟨f, hf, hn⟩ := erdos_1173_counterexample h
  obtain ⟨Y, hYfree, hYcard⟩ := hp f hf
  exact hn Y hYfree hYcard

end Erdos1173
