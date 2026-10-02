------------------------------------------------------------------------
-- Always A P s: P holds at every head of s. uncons gives P (head s)
-- and Always A P (tail s). An unfold into it takes the current stream t
-- and an invariant x : I over t; the seed is I at s.
------------------------------------------------------------------------

module Muro.ExampleAlways where

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

const0≡0 : Tm 0
const0≡0 = lam affine nat (idt nat ze ze)

isZero : Tm 0
isZero = lam affine nat (idt nat (var zero) ze)

zerosTy : Tm 0
zerosTy = stream nat

zerosTm : Tm 0
zerosTm = unf ze (lam affine nat (pair ze ze))

natsFromTy : Tm 0
natsFromTy = pi affine nat (stream nat)

natsFromTm : Tm 0
natsFromTm =
  lam affine nat
    (unf (var zero) (lam reuse nat (pair (var zero) (su (var zero)))))

-- Always Nat (λ _ → {0 ≡ 0}) zeros. The obligation does not mention the
-- stream, so the invariant can be Unit.
alwaysTy : Tm 0
alwaysTy = alw nat const0≡0 (def 0)

-- unfold tt (λ (t : Stream Nat) (_ : Unit) → (refl, tt))
alwaysTm : Tm 0
alwaysTm = unf one (lam affine (stream nat) (lam affine unit (pair rfl one)))

-- An invariant {t ≡ S} over the current stream t: the head obligation
-- and the invariant at the tail are both read off S by rewriting.
-- unfold refl (λ (t : Stream Nat) (e : {t ≡ S}) →
--   (rewrite e (x. {head x ≡ 0}) refl, rewrite e (x. {tail x ≡ S}) refl))
isStreamStep : Tm 0 → Tm 0
isStreamStep S =
  lam affine (stream nat)
    (lam affine (idt (stream nat) (var zero) (closed S))
      (pair (rwt (var zero) (idt nat (headTm (var zero)) ze) rfl)
            (rwt (var zero) (idt (stream nat) (tailTm (var zero)) (closed S)) rfl)))

isZeroTy : Tm 0
isZeroTy = alw nat isZero (def 0)

alwaysBook : Sig
alwaysBook = fromDefs (
  mkDef "zeros"             run  zerosTy  zerosTm  ∷
  mkDef "zeros-always-zero" evid alwaysTy alwaysTm ∷
  mkDef "zeros-all-zero"    evid isZeroTy (unf rfl (isStreamStep (def 0))) ∷
  [])

always-checks : checkSig! alwaysBook ≡ ok tt
always-checks = refl

-- Unguarded evidence: self-call is not an unfold.
badAlways : Sig
badAlways = fromDefs (
  mkDef "zeros" run (stream nat) zerosTm ∷
  mkDef "bad" evid (alw nat const0≡0 (def 0)) (def 1) ∷
  [])

bad-always-rejected : rejected (checkSig! badAlways) ≡ true
bad-always-rejected = refl

-- natsFrom 0 is not all zeros. Each attempt is refused: the step without
-- a stream binder, a Unit invariant (the obligation at an arbitrary
-- stream), and {t ≡ natsFrom 0}, whose head holds but whose invariant
-- fails at the tail (natsFrom 1 is not natsFrom 0).
natsAlways : Tm 0 → Sig
natsAlways p = fromDefs (
  mkDef "natsFrom" run natsFromTy natsFromTm ∷
  mkDef "nats-always-zero" evid (alw nat isZero (app (def 0) ze)) p ∷
  [])

nats-headonly-rejected :
  rejected (checkSig! (natsAlways (unf one (lam affine unit (pair rfl one))))) ≡ true
nats-headonly-rejected = refl

nats-unit-rejected :
  rejected (checkSig! (natsAlways
    (unf one (lam affine (stream nat) (lam affine unit (pair rfl one)))))) ≡ true
nats-unit-rejected = refl

nats-invariant-rejected :
  rejected (checkSig! (natsAlways (unf rfl (isStreamStep (app (def 0) ze))))) ≡ true
nats-invariant-rejected = refl
