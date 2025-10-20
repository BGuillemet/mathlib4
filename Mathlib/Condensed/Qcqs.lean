/-
Copyright (c) 2025 Benoît Guillemet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benoît Guillemet
-/
import Mathlib.CategoryTheory.Closed.Types
import Mathlib.CategoryTheory.Sites.Qcqs
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.Condensed.Functors
import Mathlib.Condensed.Limits

/-!
# Quasicompact and quasiseparated condensed sets

We give properties of quasicompact, quasiseparated and qcqs condensed sets.
-/

universe u v w

open CategoryTheory Limits Functor

namespace Condensed

attribute [local instance] Types.instConcreteCategory

variable (X : CondensedSet.{u})

noncomputable def test (j : (sectionOver X.val)ᵒᵖ) :
    (((overYoneda' X.val) ⋙ presheafToSheaf (coherentTopology CompHaus) (Type (u+1))).obj j)
    ≅ (compHausToCondensed.obj j.unop.fst.unop) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (isoSheafify _ ((isSheaf_iff_isSheaf_of_type _ _).2 (Presieve.isSheaf_comp_uliftFunctor _
    (coherentTopology.isSheaf_yoneda_obj j.unop.fst.unop)))).symm

-- not specific to condensed
@[simps!]
noncomputable def sheafToPresheafCompEvaluationObjIso {n : ℕ}
    (S : (Discrete (Fin n))ᵒᵖ ⥤ CompHausᵒᵖ) (X : CondensedSet.{u}) :
    X.val.obj (limit S)
    ≅ (limit (S ⋙ evaluation _ _ ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _))).obj X :=
  have := preservesLimitsOfShape_of_equiv (Discrete.opposite (Fin n)).symm X.val
  (preservesLimitIso X.val S).trans (limitObjIsoLimitCompEvaluation
    (S ⋙ evaluation _ _ ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _)) X).symm

-- not specific to condensed
noncomputable def sheafToPresheafCompEvaluationLimitIso {n : ℕ}
    (S : (Discrete (Fin n))ᵒᵖ ⥤ CompHausᵒᵖ) :
    sheafToPresheaf (coherentTopology CompHaus) (Type (u + 1))
    ⋙ (evaluation CompHausᵒᵖ (Type (u + 1))).obj (limit S)
    ≅ limit (S ⋙ evaluation _ _ ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _)) := by
  refine NatIso.ofComponents (sheafToPresheafCompEvaluationObjIso S) (fun {X Y} f => ?_)
  have := preservesLimitsOfShape_of_equiv (Discrete.opposite (Fin n)).symm X.val
  have := preservesLimitsOfShape_of_equiv (Discrete.opposite (Fin n)).symm Y.val
  ext x
  set F := S ⋙ evaluation CompHausᵒᵖ (Type (u + 1)) ⋙ (whiskeringLeft _ _ (Type (u + 1))).obj
    (sheafToPresheaf (coherentTopology CompHaus) (Type (u + 1)))
  change _ = ((limitObjIsoLimitCompEvaluation _ _).inv ≫ (limit F).map _) _
  rw [limitObjIsoLimitCompEvaluation_inv_limit_map F f]
  refine congrArg _ (Types.limit_ext _ _ _ (fun j => ?_))
  change ((preservesLimitIso Y.val S).hom ≫ (limit.π (S ⋙ Y.val) j)) _
    = (limMap (whiskerLeft F ((evaluation _ _).map f)) ≫ limit.π (F ⋙ (evaluation _ _).obj Y) j) _
  rw [limMap_π, preservesLimitIso_hom_π]
  change (f.val.app (limit S) ≫ Y.val.map (limit.π S j)) _ = _
  rw [← f.val.naturality (limit.π S j)]
  change _ = (F.obj j).map f (((preservesLimitIso X.val S).hom ≫ limit.π (S ⋙ X.val) j) x)
  rw [preservesLimitIso_hom_π]
  rfl

@[simp]
lemma sheafToPresheafCompEvaluationLimitIso_app {n : ℕ} (S : (Discrete (Fin n)) ⥤ CompHaus)
    (X : CondensedSet) :
    (sheafToPresheafCompEvaluationLimitIso S.op).hom.app X
    = (sheafToPresheafCompEvaluationObjIso S.op X).hom :=
  rfl

@[simp]
lemma sheafToPresheafCompEvaluationLimitIso_hom_π {n : ℕ} (S : (Discrete (Fin n)) ⥤ CompHaus.{u})
    (j : Discrete (Fin n)) :
    (sheafToPresheafCompEvaluationLimitIso S.op).hom ≫ limit.π _ (Opposite.op j)
    = (evaluation _ _ ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _)).map
    (limit.π _ (Opposite.op j)) := by
  ext X (x : X.val.obj (limit S.op))
  have := preservesLimitsOfShape_of_equiv (Discrete.opposite (Fin n)).symm X.val
  change ((preservesLimitIso X.val S.op).hom ≫ (limitObjIsoLimitCompEvaluation
    (S.op ⋙ evaluation _ _ ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf _ (Type (u + 1)))) X).inv
    ≫ ((limit.π (S.op ⋙ evaluation _ _ ⋙ (whiskeringLeft _ _ _).obj _) _).app X)) _ = _
  simp only [comp_obj, op_obj, whiskeringLeft_obj_obj, sheafToPresheaf_obj, evaluation_obj_obj,
    limitObjIsoLimitCompEvaluation_inv_π_app, types_comp_apply, Functor.comp_map,
    whiskeringLeft_obj_map, whiskerLeft_app, evaluation_map_app, ← preservesLimitIso_hom_π]
  rfl

-- not specific to condensed
noncomputable def limCompEvaluationCompWhiskeringLeftSheafToPresheafIso {n : ℕ} :
    (lim (J := (Discrete (Fin n))ᵒᵖ) (C := CompHaus.{u}ᵒᵖ))
    ⋙ evaluation CompHaus.{u}ᵒᵖ (Type (u + 1))
    ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf (coherentTopology CompHaus) _)
    ≅ (whiskeringRight _ _ _).obj
    (evaluation _ _ ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _)) ⋙ lim := by
  refine NatIso.ofComponents sheafToPresheafCompEvaluationLimitIso (fun {S T} f => ?_)
  ext X x
  set F := S ⋙ evaluation CompHausᵒᵖ (Type (u + 1)) ⋙ (whiskeringLeft _ _ (Type (u + 1))).obj
    (sheafToPresheaf (coherentTopology CompHaus) (Type (u + 1)))
  set G := T ⋙ evaluation CompHausᵒᵖ (Type (u + 1)) ⋙ (whiskeringLeft _ _ (Type (u + 1))).obj
    (sheafToPresheaf (coherentTopology CompHaus) (Type (u + 1)))
  have := preservesLimitsOfShape_of_equiv (Discrete.opposite (Fin n)).symm X.val
  change (limitObjIsoLimitCompEvaluation G X).inv
    ((preservesLimitIso X.val T).hom (X.val.map (limMap f) x)) =
    ((preservesLimitIso X.val S).hom ≫ (limitObjIsoLimitCompEvaluation F X).inv ≫
    (limMap (whiskerRight f (_ ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _)))).app X
    ≫ (𝟙 _)) x
  rw [← (limitObjIsoLimitCompEvaluation G X).hom_inv_id]
  refine congrArg _ (Types.limit_ext _ _ _ (fun j => ?_))
  change _ = ((limitObjIsoLimitCompEvaluation G X).hom ≫ limit.π (G ⋙ (evaluation _ _).obj X) j) _
  rw [limitObjIsoLimitCompEvaluation_hom_π]
  change _ = (limMap _ ≫ limit.π G j).app X _
  rw [limMap_π]
  change _ =
    X.val.map (f.app j) (((limitObjIsoLimitCompEvaluation F X).inv ≫ (limit.π F j).app X) _)
  rw [limitObjIsoLimitCompEvaluation_inv_π_app]
  change (X.val.map _ ≫ (preservesLimitIso X.val T).hom ≫ limit.π _ j) x =
    X.val.map (f.app j) (((preservesLimitIso X.val S).hom ≫ limit.π _ j) x)
  rw [preservesLimitIso_hom_π, preservesLimitIso_hom_π, ← X.val.map_comp]
  simp

noncomputable def limCompValNatIso {n : ℕ} (X : CondensedSet.{u}) :
    lim ⋙ X.val ≅ (whiskeringRight (Discrete (Fin n)) _ _).obj X.val ⋙ lim :=
  preservesLimitNatIso X.val

def condensedYonedaEquiv {S : CompHaus.{u}} {X : CondensedSet.{u}} :
    (compHausToCondensed.obj S ⟶ X) ≃ X.val.obj (Opposite.op S) :=
  (coherentTopology CompHaus).uliftYonedaEquiv

noncomputable def condensedYonedaLemma :
    compHausToCondensed.op ⋙ coyoneda
      ≅ evaluation _ _ ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _) :=
  (coherentTopology CompHaus).largeCurriedUliftYonedaLemma.trans
    (isoWhiskerLeft _ (isoWhiskerRight ((whiskeringRight _ _ _).mapIso uliftFunctorTrivial) _))

@[simp]
lemma condensedYonedaLemma_app_app (S : CompHaus.{u}) (X : CondensedSet.{u}) :
    (condensedYonedaLemma.app (Opposite.op S)).app X
    = condensedYonedaEquiv.toIso :=
  rfl

noncomputable def coyonedaOpCompHausToCondensedFiniteCoproductNatIso {n : ℕ}
    (S : Discrete (Fin n) ⥤ CompHaus.{u}) :
    coyoneda.obj (Opposite.op (compHausToCondensed.obj (colimit S)))
    ≅ coyoneda.obj (Opposite.op (colimit (S ⋙ compHausToCondensed))) :=
  (condensedYonedaLemma.app (Opposite.op (colimit S))).trans
    (((_ ⋙ _).mapIso (limitOpIsoOpColimit _).symm).trans
    ((sheafToPresheafCompEvaluationLimitIso S.op).trans
    (((HasLimit.isoOfNatIso (isoWhiskerLeft S.op condensedYonedaLemma.symm))).trans
    ((preservesLimitIso coyoneda (S ⋙ compHausToCondensed).op).symm.trans
    (coyoneda.mapIso (limitOpIsoOpColimit _))))))

@[simp]
lemma coyonedaOpCompHausToCondensedFiniteCoproductNatIso_hom {n : ℕ}
    (S : Discrete (Fin n) ⥤ CompHaus.{u}) :
    (coyonedaOpCompHausToCondensedFiniteCoproductNatIso S).hom
    = coyoneda.map (colimit.post S compHausToCondensed).op := by
  unfold coyonedaOpCompHausToCondensedFiniteCoproductNatIso
  simp only [comp_obj, op_obj, whiskeringLeft_obj_obj, mapIso_symm, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, mapIso_inv, Functor.comp_map, whiskeringLeft_obj_map, ← Category.assoc]
  rw [← Iso.eq_comp_inv, Iso.comp_inv_eq, ← Iso.eq_comp_inv]
  apply limit.hom_ext fun j => ?_
  simp only [comp_obj, op_obj, whiskeringLeft_obj_obj, Category.assoc, mapIso_inv]
  rw [sheafToPresheafCompEvaluationLimitIso_hom_π]
  ext X (f : compHausToCondensed.obj (colimit S) ⟶ X)
  have h₁ : (condensedYonedaLemma.hom.app (Opposite.op (colimit S))).app X f
      = condensedYonedaEquiv f := rfl
  have h₂ : X.val.map (limit.π S.op j)
      (X.val.map (limitOpIsoOpColimit S).inv (condensedYonedaEquiv f))
      = condensedYonedaEquiv (compHausToCondensed.map (colimit.ι S j.unop) ≫ f) := by
    change (f.val.app _ ≫ _ ≫ _) _ = _
    rw [← X.val.map_comp, ← f.val.naturality, limitOpIsoOpColimit_inv_comp_π]
    rfl
  simp only [comp_obj, sheafToPresheaf_obj, evaluation_obj_obj, Opposite.op_unop, op_obj,
    Functor.comp_map, whiskeringLeft_obj_map, FunctorToTypes.comp, whiskerLeft_app,
    evaluation_map_app, coyoneda_map_app, Quiver.Hom.unop_op]
  change _ = ((preservesLimitIso coyoneda (S ⋙ compHausToCondensed).op).hom
    ≫ (HasLimit.isoOfNatIso (S.op.isoWhiskerLeft condensedYonedaLemma.symm)).inv
    ≫ limit.π _ j).app X _
  rw [h₁, h₂, HasLimit.isoOfNatIso_inv_π]
  change _ = (((preservesLimitIso coyoneda (S ⋙ compHausToCondensed).op).hom
    ≫ limit.π _ j)
    ≫ (S.op.isoWhiskerLeft condensedYonedaLemma.symm).inv.app j).app X _
  rw [preservesLimitIso_hom_π]
  simp only [comp_obj, op_obj, whiskeringLeft_obj_obj, sheafToPresheaf_obj, evaluation_obj_obj,
    isoWhiskerLeft_inv, Iso.symm_inv, whiskerLeft_app, FunctorToTypes.comp, coyoneda_map_app]
  rw [← Category.assoc, ← unop_comp, limitOpIsoOpColimit_inv_comp_π, Quiver.Hom.unop_op,
    colimit.ι_post_assoc]
  rfl

noncomputable def coyonedaOpCompHausToCondensedFiniteCoproductNatIso' {n : ℕ}
    (S : Fin n → CompHaus.{u}) :
    coyoneda.obj (Opposite.op (compHausToCondensed.obj (∐ S)))
    ≅ coyoneda.obj (Opposite.op (∐ compHausToCondensed.obj ∘ S)) :=
  (coyonedaOpCompHausToCondensedFiniteCoproductNatIso (Discrete.functor S)).trans
    (coyoneda.mapIso (HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete _ _).symm).op)

noncomputable def compHausToCondensedFiniteCoproductIso {n : ℕ}
    (S : Discrete (Fin n) ⥤ CompHaus.{u}) :
    compHausToCondensed.obj (colimit S) ≅ colimit (S ⋙ compHausToCondensed) :=
  (Coyoneda.fullyFaithful.preimageIso
    (coyonedaOpCompHausToCondensedFiniteCoproductNatIso S).symm).unop

@[simp]
lemma compHausToCondensedFiniteCoproductIso_inv {n : ℕ} (S : Discrete (Fin n) ⥤ CompHaus.{u}) :
    (compHausToCondensedFiniteCoproductIso S).inv = colimit.post S compHausToCondensed := by
  simp [compHausToCondensedFiniteCoproductIso]

instance {n : ℕ} (S : Discrete (Fin n) ⥤ CompHaus.{u}) :
    IsIso (colimit.post S compHausToCondensed) := by
  rw [← compHausToCondensedFiniteCoproductIso_inv]
  infer_instance

noncomputable def compHausToCondensedFiniteCoproductIso' {n : ℕ} (S : Fin n → CompHaus.{u}) :
    compHausToCondensed.obj (∐ S) ≅ ∐ (compHausToCondensed.obj ∘ S) :=
  (Coyoneda.fullyFaithful.preimageIso
    (coyonedaOpCompHausToCondensedFiniteCoproductNatIso' S).symm).unop

noncomputable def compHausToCondensedFiniteCoproductIso'' {n : ℕ} :
    colim (J := Discrete (Fin n)) ⋙ compHausToCondensed
    ≅ (whiskeringRight _ _ _).obj compHausToCondensed ⋙ colim := by
  apply NatIso.removeOp
  refine ((Functor.opComp _ _).trans ?_).trans (Functor.opComp colim compHausToCondensed).symm
  apply fullyFaithfulCancelRight coyoneda
  refine Iso.trans ?_ (isoWhiskerLeft colim.op condensedYonedaLemma).symm
  refine Iso.trans ?_ (isoWhiskerRight opHomCompLimNatIsoColimOp (_ ⋙ _))
  refine Iso.trans ?_ (isoWhiskerLeft _ limCompEvaluationCompWhiskeringLeftSheafToPresheafIso).symm
  refine Iso.trans ?_ (isoWhiskerLeft _ (isoWhiskerRight (mapIso _ condensedYonedaLemma) lim))
  refine Iso.trans (isoWhiskerRight (isoWhiskerLeft _ opHomCompLimNatIsoColimOp.symm) coyoneda) ?_
  change (((whiskeringRight _ _ _).obj _).op ⋙ opHom _ _) ⋙ (lim ⋙ coyoneda) ≅ _
  refine Iso.trans (isoWhiskerLeft _ (preservesLimitNatIso coyoneda)) ?_
  refine Iso.trans (isoWhiskerRight (whiskeringRightObjOpCompOpHom _) _) ?_
  rw [← whiskeringRight_obj_comp]
  rfl

instance : PreservesFiniteCoproducts compHausToCondensed.{u} where
  preserves _ :=  { preservesColimit := preservesColimit_of_isIso_post _ _ }

lemma preservesColimitIso_compHausToCondensed {n : ℕ} (S : Discrete (Fin n) ⥤ CompHaus.{u}) :
    preservesColimitIso compHausToCondensed.{u} S = compHausToCondensedFiniteCoproductIso S := by
  refine Iso.symm_eq_iff.1 (Iso.ext (colimit.hom_ext ?_))
  simp

theorem isQuasicompact_iff_compHaus_cover (X : CondensedSet.{u}) :
    X.Quasicompact ↔ ∃ S : CompHaus.{u}, ∃ f : compHausToCondensed.obj S ⟶ X, Epi f := by
  constructor
  · intro hX
    obtain ⟨J, hJ⟩ := hX.exists_finset_epi
      (Limits.sigmaMapColim (overYoneda' X.val ⋙ presheafToSheaf _ _)
      ≫ (Sheaf.isoColimitOverYonedaCompPresheafToSheaf'.{u + 1} X).inv)
    obtain ⟨n, hn⟩ := Finite.exists_equiv_fin J
    obtain e := Classical.choice hn
    use ∐ (fun j : Fin n => (e.invFun j).val.unop.fst.unop)
    have (j : Fin n) : compHausToCondensed.obj (e.invFun j).val.unop.fst.unop
        ≅ (overYoneda' X.val ⋙ presheafToSheaf _ _).obj (e.invFun j) := by
      change compHausToCondensed.obj (e.invFun j).val.unop.fst.unop
        ≅ (yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u + 1} ⋙ presheafToSheaf _ _).obj
        (e.invFun j).val.unop.fst.unop
      apply Iso.app
      exact isoWhiskerLeft (_ ⋙ sheafCompose _ _) (sheafificationNatIso _ _) ≪≫
        isoWhiskerRight (coherentTopology CompHaus).uliftYonedaCompSheafToPresheaf
        (presheafToSheaf _ _)
    use ((compHausToCondensedFiniteCoproductIso' _).hom
      ≫ (Sigma.mapIso this).hom
      ≫ (Sigma.whiskerEquiv (g := (overYoneda' X.val ⋙ presheafToSheaf _ _).obj ∘ Subtype.val)
      e.symm (fun _ => Iso.refl _)).hom)
      ≫ Sigma.map' Subtype.val (fun j => 𝟙 _)
      ≫ sigmaMapColim (overYoneda' X.val ⋙ presheafToSheaf _ _)
      ≫ (Sheaf.isoColimitOverYonedaCompPresheafToSheaf'.{u + 1} X).inv
    exact epi_comp' inferInstance hJ
  · intro ⟨S, f, hf⟩
    refine { exists_finset_epi := fun {I G} g hg => ?_ }

    sorry

end Condensed
