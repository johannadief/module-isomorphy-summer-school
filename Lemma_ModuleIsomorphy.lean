import Mathlib

/-!
#Modullemma -/

--first a few results to use in the final proof

theorem finitedimensional_isArtinian
  (K C : Type*) [Field K] [Ring C] [Algebra K C]
  [IsSimpleRing C] [FiniteDimensional K C] : IsArtinianRing C := by
  have hK : IsArtinian K C := by
    infer_instance
  exact isArtinian_of_tower K hK

theorem simple_artinian_semisimple
  (C : Type*) [Ring C] [IsSimpleRing C] [IsArtinianRing C] : IsSemisimpleRing C := by
  infer_instance

theorem simple_artinian_semisimple_module
  (K C : Type*) [Field K] [Ring C] [Algebra K C] [IsSemisimpleRing C] [FiniteDimensional K C]
  (M : Type*) [AddCommGroup M] [Module C M] [Module K M] [IsScalarTower K C M]
  [FiniteDimensional K M] : IsSemisimpleModule C M := by
    infer_instance

theorem module_finite
  (K C : Type*) [Field K] [Ring C] [Algebra K C]
  [IsSemisimpleRing C] [FiniteDimensional K C] (M : Type*) [AddCommGroup M] [Module C M]
  [Module K M] [IsScalarTower K C M] [FiniteDimensional K M] : Module.Finite C M := by
    exact Module.Finite.of_restrictScalars_finite K C M


theorem module_isomorphic_to_simple_module
  (K C : Type*) [Field K] [Ring C] [Algebra K C] [IsSimpleRing C] [FiniteDimensional K C]
  (M : Type*) [AddCommGroup M] [Module C M] [Module K M] [IsScalarTower K C M]
  [FiniteDimensional K M] [Nontrivial M] : ∃ n, ∃ (_ : NeZero n), ∃ S : Submodule C M,
  IsSimpleModule C ↥S ∧ Nonempty (M ≃ₗ[C] Fin n → ↥S) := by
    have h1 := finitedimensional_isArtinian K C
    have h2 := simple_artinian_semisimple C
    have h3 := simple_artinian_semisimple_module K C M
    have h4 := module_finite K C M
    have h5 : IsIsotypic C M := by apply IsSimpleRing.isIsotypic
    exact IsIsotypic.linearEquiv_fun (R:=C) (M := M) h5



theorem module_isomorphy
  (K C : Type*) [Field K] [Ring C] [Algebra K C] [IsSimpleRing C] [FiniteDimensional K C]
  (M M' : Type*) [AddCommGroup M] [Module C M] [Module K M] [IsScalarTower K C M]
  [FiniteDimensional K M] [AddCommGroup M'] [Module K M'] [Module C M'] [IsScalarTower K C M']
  [FiniteDimensional K M'] (hdim : Module.finrank K M = Module.finrank K M') [Nontrivial M]
  [Nontrivial M'] :
    -- Conclusion: M and M' are C-isomorphic (there exists a linear isomorphism of C-modules)
    Nonempty (M ≃ₗ[C] M') := by
--use theorem module_isomorphic_to_simple_module to get n, S and isomorphism for M and M'
    have h1 : ∃ n, ∃ (_ : NeZero n), ∃ S : Submodule C M,
    IsSimpleModule C ↥S ∧ Nonempty (M ≃ₗ[C] Fin n → ↥S) := by
      exact module_isomorphic_to_simple_module K C M
    have h2 : ∃ n', ∃ (_ : NeZero n'), ∃ S' : Submodule C M',
    IsSimpleModule C ↥S' ∧ Nonempty (M' ≃ₗ[C] Fin n' → ↥S') := by
      exact module_isomorphic_to_simple_module K C M'
-- Choose n, S and isomorphism for M and M'
    obtain ⟨ n, hn, S, hS, hM ⟩ := h1
    obtain ⟨ n', hn', S', hS', hM' ⟩ := h2
-- create copy of hdim to use in the proof (rewrite)
    have hdimM : Module.finrank K M = Module.finrank K M' := by exact hdim
--show that S^n and S'^n' have the same dimension over K
    have hdimFin : Module.finrank K (Fin n → ↥S) = Module.finrank K (Fin n' → ↥S') := by
        --isomorphism of M and S^n and M' and S'^n'
        obtain ⟨h1⟩ := hM
        obtain ⟨h2⟩ := hM'
        -- have to show that if finrank C is the same then also finrank K
        have h3 : Module.finrank K (Fin n → ↥S) = Module.finrank K M := by
          exact (h1.restrictScalars K).finrank_eq.symm
        have h4 : Module.finrank K (Fin n' → ↥S') = Module.finrank K M' := by
          exact (h2.restrictScalars K).finrank_eq.symm
        rw [← h3, ← h4] at hdimM
        exact hdimM
--now we can show that S and S' have the same dimension over K
--for that we need to show that S and S' are finite dimensional over K
    have : FiniteDimensional K S := by
        apply FiniteDimensional.of_injective ((Submodule.subtype S).restrictScalars K)
        exact Submodule.subtype_injective S
--and use that the dimension of S^n is n*S
    have h5 : Module.finrank K (Fin n → ↥S) = n * Module.finrank K ↥S := by
        rw [Module.finrank_pi_fintype]
        simp
    have : FiniteDimensional K S' := by
        apply FiniteDimensional.of_injective ((Submodule.subtype S').restrictScalars K)
        exact Submodule.subtype_injective S'
    have h6 : Module.finrank K (Fin n' → ↥S') = n' * Module.finrank K ↥S' := by
        rw [Module.finrank_pi_fintype]
        simp
-- rewrite hdimFin using h5 and h6 to get n * dim_K S = n' * dim_K S'
    rw [h5, h6] at hdimFin
-- implement that C is Artinian and semisimple
    have : IsArtinianRing C := by
      exact finitedimensional_isArtinian K C
    have : IsSemisimpleRing C := by
      exact simple_artinian_semisimple C
-- give explicit name to S ans S' being simple
    let : IsSimpleModule C S := hS
    let : IsSimpleModule C S' := hS'
-- since C is semisimple and S simple, there exists an ideal I that is isomorphic to S as C-module
    obtain ⟨I, hSI⟩ :=
       IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule C S
    obtain ⟨eSI⟩ := hSI
-- similarily for S'
    obtain ⟨J, hS'J⟩ :=
       IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule C S'
    obtain ⟨eS'J⟩ := hS'J
-- I and J are simple modules since they are isomorphic to S and S' which are simple
    have : IsSimpleModule C I := by
       exact eSI.isSimpleModule_iff.mp hS
    have : IsSimpleModule C J := by
       exact eS'J.isSimpleModule_iff.mp hS'
-- C is isotypic as module over itself because it is simple and artinian
    have hC : IsIsotypic C C := by
       exact IsSimpleRing.isIsotypic C C
-- Since C is isotypic all its simple submodules are isomorphic, in particular I and J
    have hIJ : Nonempty (I ≃ₗ[C] J) := by
       exact (hC J) I
    obtain ⟨eIJ⟩ := hIJ
-- Per transitivity of isomorphisms we get that S and S' are isomorphic over C
    have eSS' : S ≃ₗ[C] S' :=
      (eSI.trans eIJ).trans eS'J.symm
-- Then they also have the same dimension over K
    have hdimS : Module.finrank K ↥S = Module.finrank K ↥S' := by
      exact (eSS'.restrictScalars K).finrank_eq
-- Now show that S^n and S'^n' have the same dimension over K
    have hdimFin : Module.finrank K (Fin n → ↥S) = Module.finrank K (Fin n' → ↥S') := by
      obtain ⟨h1⟩ := hM
      obtain ⟨h2⟩ := hM'
        -- have to show that if finrank C is the same then also finrank K
      have h3 : Module.finrank K (Fin n → ↥S) = Module.finrank K M := by
        exact (h1.restrictScalars K).finrank_eq.symm
      have h4 : Module.finrank K (Fin n' → ↥S') = Module.finrank K M' := by
        exact (h2.restrictScalars K).finrank_eq.symm
      rw [← h3, ← h4] at hdim
      exact hdim
-- Now we can show that n = n':
    have hnn' : n = n' := by
      -- n * dim S = n' * dim S'
      have hnn'_eq : n * Module.finrank K ↥S = n' * Module.finrank K ↥S' := by
        rw [h5, h6] at hdimFin
        exact hdimFin
      -- S' is simple and nontrivial, so its dimension over K is greater than 0
      let : IsSimpleModule C S' := hS'
      let : Nontrivial S' := IsSimpleModule.nontrivial C S'
      have hS'_pos : 0 < Module.finrank K S' := by
        exact Module.finrank_pos
      -- so we can replace dim S' with dim S and n = n' follows
      rw [hdimS] at hnn'_eq
      exact Nat.mul_right_cancel hS'_pos hnn'_eq
-- We have M isomorphic to S^n' and M' isomorphiy to S'^n'
    obtain ⟨eM⟩ := hM
    obtain ⟨eM'⟩ := hM'
    rw[hnn'] at eM
-- construct isomorphism for every component of S^n and S'^n' using the isomorphism between S and S'
    have ePi : (Fin n' → S) ≃ₗ[C] (Fin n' → S') :=
      LinearEquiv.piCongrRight fun _ => eSS'
-- Per transitivity M - S^n' - S'^n' - M' we get that M and M' are isomorphic over C
    exact ⟨(eM.trans ePi).trans eM'.symm⟩
