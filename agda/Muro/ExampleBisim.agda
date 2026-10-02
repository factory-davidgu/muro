------------------------------------------------------------------------
-- Stream bisimilarity: σ ~ τ at A. uncons gives {head σ ≡ head τ : A}
-- and tail σ ~ tail τ. An unfold into it takes the current streams a, b
-- and an invariant x : I over them; the seed is I at σ, τ.
--
-- J.J.M.M. Rutten, Elements of Stream Calculus (An Extensive Exercise
-- in Coinduction), ENTCS 45 (2001), Theorem 2.1.
------------------------------------------------------------------------

module Muro.ExampleBisim where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Fin.Base using (zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst
open import Muro.Check

rejected : Result ⊤ → Bool
rejected (ok _)   = false
rejected (fail _) = true

-- The invariant {a ≡ b : Stream Nat}: equal streams are bisimilar.
-- λ (a b : Stream Nat) (e : {a ≡ b}) →
--   (rewrite e (x. {head x ≡ head b}) refl, rewrite e (x. {tail x ≡ tail b}) refl)
eqStep : Tm 0
eqStep =
  lam affine (stream nat)
    (lam affine (stream nat)
      (lam affine (idt (stream nat) (var (suc zero)) (var zero))
        (pair (rwt (var zero) (idt nat (headTm (var zero)) (headTm (var (suc (suc zero))))) rfl)
              (rwt (var zero) (idt (stream nat) (tailTm (var zero)) (tailTm (var (suc (suc zero))))) rfl))))

zerosTy : Tm 0
zerosTy = stream nat

zerosTm : Tm 0
zerosTm = unf ze (lam affine nat (pair ze ze))

zerosBisimTy : Tm 0
zerosBisimTy = bsm nat (def 0) (def 1)

-- unfold refl eqStep
zerosBisimTm : Tm 0
zerosBisimTm = unf rfl eqStep

zerosBook : Sig
zerosBook = fromDefs (
  mkDef "zeros"       run  zerosTy      zerosTm      ∷
  mkDef "zeros'"      run  zerosTy      zerosTm      ∷
  mkDef "zeros-bisim" evid zerosBisimTy zerosBisimTm ∷
  [])

zeros-bisim-checks : checkSig! zerosBook ≡ ok tt
zeros-bisim-checks = refl

natsFromTy : Tm 0
natsFromTy = pi affine nat (stream nat)

natsFromTm : Tm 0
natsFromTm =
  lam affine nat
    (unf (var zero) (lam reuse nat (pair (var zero) (su (var zero)))))

natsTailTy : Tm 0
natsTailTy =
  pi affine nat
    (bsm nat
      (tailTm (app (def 0) (var zero)))
      (app (def 0) (su (var zero))))

natsTailTm : Tm 0
natsTailTm = lam affine nat (unf rfl (closed eqStep))

natsBook : Sig
natsBook = fromDefs (
  mkDef "natsFrom"        run  natsFromTy natsFromTm ∷
  mkDef "nats-tail-bisim" evid natsTailTy natsTailTm ∷
  [])

nats-tail-bisim-checks : checkSig! natsBook ≡ ok tt
nats-tail-bisim-checks = refl

-- natsFrom 0 ~ zeros is refused: the step without stream binders, a
-- Unit invariant (equal heads of arbitrary streams), and {a ≡ b} (the
-- seed would need natsFrom 0 ≡ zeros).
natsZeros : Tm 0 → Sig
natsZeros p = fromDefs (
  mkDef "natsFrom" run natsFromTy natsFromTm ∷
  mkDef "zeros"    run zerosTy    zerosTm    ∷
  mkDef "nats-bisim-zeros" evid (bsm nat (app (def 0) ze) (def 1)) p ∷
  [])

nats-zeros-headonly-rejected :
  rejected (checkSig! (natsZeros (unf one (lam affine unit (pair rfl one))))) ≡ true
nats-zeros-headonly-rejected = refl

nats-zeros-unit-rejected :
  rejected (checkSig! (natsZeros
    (unf one (lam affine (stream nat) (lam affine (stream nat) (lam affine unit (pair rfl one))))))) ≡ true
nats-zeros-unit-rejected = refl

nats-zeros-eq-rejected : rejected (checkSig! (natsZeros (unf rfl eqStep))) ≡ true
nats-zeros-eq-rejected = refl
