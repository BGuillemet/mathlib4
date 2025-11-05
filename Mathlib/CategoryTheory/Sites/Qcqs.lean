/-
Copyright (c) 2025 Benoît Guillemet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benoît Guillemet
-/
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Coherent.Basic
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Quasicompact and quasiseparated sheaves

Given a site `(C, J)`, we define structures for being quasicompact, quasiseparated
or qcqs sheaves.

-/

universe u v u' v' w

section

open CategoryTheory Limits

variable {I : Type} {C : Type u} [Category.{v} C]

noncomputable def Types.coproductPullbackEquiv {X : I → Type} {Y Z : Type} (f : (i : I) → X i ⟶ Z)
    (g : Y ⟶ Z) : ∐ (fun i : I => pullback (f i) g) ≃ pullback (Sigma.desc f) g := by
  refine (Types.coproductIso _).toEquiv.trans
    ((Equiv.sigmaCongrRight (fun _ => (Types.pullbackIsoPullback _ _).toEquiv)).trans ?_)
  refine Equiv.trans ?_ (((Types.pullbackIsoPullback _ _).symm
    ≪≫ asIso (pullback.map (fun ⟨i, x⟩ => f i x) g (Sigma.desc f) g
    (Types.coproductIso _).inv (𝟙 _) (𝟙 _) (by ext ⟨_, _⟩; simp) rfl)).toEquiv)
  exact {
    toFun := fun ⟨j, ⟨x, y⟩, h⟩ => ⟨⟨⟨j, x⟩, y⟩, h⟩
    invFun := fun ⟨⟨⟨j, x⟩, y⟩, h⟩ => ⟨j, ⟨⟨x, y⟩, h⟩⟩ }

@[reassoc (attr := simp)]
theorem Types.ι_coproductPullbackEquiv {X : I → Type} {Y Z : Type} (f : (i : I) → X i ⟶ Z)
    (g : Y ⟶ Z) (j : I) :
    Sigma.ι (fun i => pullback (f i) g) j ≫ Types.coproductPullbackEquiv f g
      = pullback.map (f j) g (Sigma.desc f) g (Sigma.ι X j) (𝟙 _) (𝟙 _) (by simp) rfl := by
  ext <;> (unfold coproductPullbackEquiv; simp)

-- @[reassoc (attr := simp)]
-- theorem Types.ι_coproductPullbackEquiv' {X : I → Type} {Y Z : Type} (f : (i : I) → X i ⟶ Z)
--     (g : Y ⟶ Z) (j : Discrete I) :
--     colimit.ι (Discrete.functor fun i => pullback (f i) g) j ≫ Types.coproductPullbackEquiv f g
--       = pullback.map (f j.as) g (Sigma.desc f) g (Sigma.ι X j.as) (𝟙 _) (𝟙 _) (by simp) rfl :=
--   Types.ι_coproductPullbackEquiv _ _ _

noncomputable def FunctorToTypes.coproductPullbackIso (X : I → C ⥤ Type) (Y Z : C ⥤ Type)
    (f : (i : I) → X i ⟶ Z) (g : Y ⟶ Z) :
    (∐ fun i : I => pullback (f i) g) ≅ pullback (Sigma.desc f) g := by
  refine NatIso.ofComponents (fun c =>
    sigmaObjIso _ _ ≪≫ Sigma.mapIso (fun i => pullbackObjIso (f i) g c)
    ≪≫ (Types.coproductPullbackEquiv (fun i => (f i).app c) (g.app c)).toIso
    ≪≫ asIso (pullback.map _ _ _ _ (sigmaObjIso _ _).inv (𝟙 _) (𝟙 _) (by ext _ : 1; simp) rfl)
    ≪≫ (pullbackObjIso _ _ _).symm)
    fun h => ?_
  unfold sigmaObjIso pullbackObjIso
  simp only [Iso.trans_symm, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc,
    colimit_map_colimitObjIsoColimitCompEvaluation_hom_assoc,
    limitObjIsoLimitCompEvaluation_inv_limit_map]
  simp only [← Category.assoc _ _ (limitObjIsoLimitCompEvaluation _ _).inv]
  refine congrArg (fun m => (_ ≫ m) ≫ _) (colimit.hom_ext fun j => limit.hom_ext fun k => ?_)
  simp only [Functor.mapIso_hom, colim_map, Equiv.toIso_hom, ι_colimMap_assoc,
    HasColimit.isoOfNatIso_ι_hom_assoc]
  rw [Types.ι_coproductPullbackEquiv_assoc, Types.ι_coproductPullbackEquiv_assoc]
  cases k with | none => simp | some k => cases k <;> simp

end

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A] [HasWeakSheafify J A] [Limits.HasColimits A]

section Quasicompact

/-- A sheaf `F` is quasicompact if any cover `∐ G ⟶ F` admits a finite subcover. -/
structure Quasicompact (F : Sheaf J A) : Prop where
  exists_finset_epi : ∀ {I : Type v'} {G : I → Sheaf J A} (f : ∐ G ⟶ F) [Epi f],
    ∃ J : Finset I, Epi ((Limits.Sigma.map' Subtype.val (fun (j : J) => 𝟙 (G j))) ≫ f)

-- lemma idk {F : Sheaf J A} (hF : Quasicompact F) {I : Type v'} {G : I → Sheaf J A}
--     {S : (i : I) → G i ⟶ F} (hS : Sieve.ofArrows G S ∈ canonicalTopology (Sheaf J A) F) :
--     ∃ I' : Finset I,
--       Sieve.ofArrows (G ∘ Subtype.val) (fun i : I' => S i) ∈ canonicalTopology (Sheaf J A) F := by
--   sorry

lemma exists_finset_epi (F : Sheaf J A) (hF : Quasicompact F) {I : Type v'} {G : I → Sheaf J A}
    (f : ∐ G ⟶ F) [Epi f] :
    ∃ J : Finset I, Epi ((Limits.Sigma.map' Subtype.val (fun (j : J) => 𝟙 (G j))) ≫ f) :=
  hF.exists_finset_epi f

variable (I : Type)

instance Types.epi_pullback_of_epi_f {X Y Z : Type} (f : X ⟶ Z) (g : Y ⟶ Z) [Epi f] :
    Epi (Limits.pullback.snd f g) := by
  refine (epi_iff_surjective _).2 (fun y => ?_)
  obtain ⟨x, hx⟩ := (epi_iff_surjective f).1 inferInstance (g y)
  exact ⟨(Limits.Types.pullbackIsoPullback f g).inv ⟨⟨x, y⟩, hx⟩,
    Limits.Types.pullbackIsoPullback_inv_snd_apply _ _ _⟩

instance Types.epi_pullback_of_epi_g {X Y Z : Type} (f : X ⟶ Z) (g : Y ⟶ Z) [Epi g] :
    Epi (Limits.pullback.fst f g) := by
  refine (epi_iff_surjective _).2 (fun x => ?_)
  obtain ⟨y, hy⟩ := (epi_iff_surjective g).1 inferInstance (f x)
  exact ⟨(Limits.Types.pullbackIsoPullback f g).inv ⟨⟨x, y⟩, hy.symm⟩,
    Limits.Types.pullbackIsoPullback_inv_fst_apply _ _ _⟩

instance FunctorToTypes.epi_pullback_of_epi_f {X Y Z : C ⥤ Type} (f : X ⟶ Z) (g : Y ⟶ Z) [Epi f] :
    Epi (Limits.pullback.snd f g) := by
  have (c : C) : Epi ((Limits.pullback.snd f g).app c) := by
    have : Epi (Limits.pullback.snd (f.app c) (g.app c)) :=
      Types.epi_pullback_of_epi_f _ _
    rw [← Limits.pullbackObjIso_hom_comp_snd]
    infer_instance
  exact NatTrans.epi_of_epi_app _

instance FunctorToTypes.epi_pullback_of_epi_g {X Y Z : C ⥤ Type} (f : X ⟶ Z) (g : Y ⟶ Z) [Epi g] :
    Epi (Limits.pullback.fst f g) := by
  have (c : C) : Epi ((Limits.pullback.fst f g).app c) := by
    have : Epi (Limits.pullback.fst (f.app c) (g.app c)) :=
      Types.epi_pullback_of_epi_g _ _
    rw [← Limits.pullbackObjIso_hom_comp_fst]
    infer_instance
  exact NatTrans.epi_of_epi_app _

lemma quasicompact_of_epi_quasicompact [Limits.HasPullbacks A] {F F' : Sheaf J A} (f : F' ⟶ F)
    [Epi f] (hF' : F'.Quasicompact) : F.Quasicompact where
  exists_finset_epi {I G} g [Epi g] := by
    set G' := fun i : I => Limits.pullback (Limits.Sigma.ι G i ≫ g) f
    set g' := Limits.Sigma.desc fun i => Limits.pullback.snd (Limits.Sigma.ι G i ≫ g) f
    have : Epi (Limits.pullback.fst f g) := by
      sorry
    sorry

lemma quasicompact_of_finite_presieve_quasicompact [Limits.HasPullbacks A] {F : Sheaf J A}
    {I : Type v'} (hI : Fintype I) {G : I → Sheaf J A} (hG : ∀ i : I, Quasicompact (G i))
    (f : ∐ G ⟶ F) [Epi f] : F.Quasicompact where
  exists_finset_epi {I' G'} f' [Epi f'] := by
    /- #check (fun i : I => (hG i).exists_finset_epi (Limits.pullback.snd f' (Limits.Sigma.ι G i ≫ f)))
    choose J' hJ' using (fun i : I => (hG i).exists_finset_epi (Limits.pullback.snd f' (Limits.Sigma.ι G i ≫ f))) -/
    sorry

end Quasicompact

variable [Limits.HasPullbacks A]

section Quasiseparated

/-- A morphism of sheaves `g : G ⟶ F` is quasicompact if the pullback of any morphism `F' ⟶ F`
  with quasicompact source is again quasicompact. -/
structure QuasicompactMap {F G : Sheaf J A} (g : G ⟶ F) : Prop where
  quasicompact_pullback : ∀ (F' : Sheaf J A) (f : F' ⟶ F),
    F'.Quasicompact → (Limits.pullback f g).Quasicompact

/-- A sheaf `F` is quasiseparated if any morphism `F' ⟶ F` with quasicompact source is
  quasicompact. -/
structure Quasiseparated (F : Sheaf J A) : Prop where
  quasicompactMap_of_quasicompact (F' : Sheaf J A) (f : F' ⟶ F) (hF' : F'.Quasicompact) :
    QuasicompactMap f

lemma quasicompactMap_of_quasicompact (F : Sheaf J A) (hF : Quasiseparated F) (F' : Sheaf J A)
    (f : F' ⟶ F) (hF' : F'.Quasicompact) : QuasicompactMap f :=
  hF.quasicompactMap_of_quasicompact F' f hF'

end Quasiseparated

section Qcqs

/-- A sheaf `F` is qcqs if it is both quasicompact and quasiseparated. -/
structure Qcqs (F : Sheaf J A) : Prop extends F.Quasicompact, F.Quasiseparated

end Qcqs

end CategoryTheory.Sheaf
