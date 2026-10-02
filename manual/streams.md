---
title: Streams
slug: streams
order: 8
summary: ν, unfold, Always, and bisimulation.
---

# Streams

In brief: μ descends (`match` on Nat). ν is a greatest fixed point. Stream is `ν X. A × X`. Only a `run` Stream becomes an Elixir `Stream`. A non-productive unfold is rejected. `Always` and `~` are indexed by streams; an unfold into them carries an invariant over the current stream.

## ν Stream

There is one ν former. The block is required for shape, then dropped — Stream is primitive.

```
ν Stream (A : Type) : Type where
  uncons : Stream A → A × Stream A
```

ASCII: `nu Stream (A : Type) : Type where uncons : Stream A -> A * Stream A`.

`uncons` splits a stream into a head and a tail. `head` and `tail` are sugar for `fst (uncons s)` and `snd (uncons s)`, that is, for a `let` on `uncons s` (see [Terms](language.md#products)).

## unfold

A ν value must be an `unfold`.

```
unfold seed (λ (s : S) → (head, next_seed))
```

The body is a pair. Productivity: in `run` and `evidence`, the self-name of the definition must not occur in the pair’s **head**. The tail may continue the stream. Spec does not run this check.

`+` is still only for Data. You may write `(+ k : Nat)` in an unfold step when the seed is Nat.

### zeros

```
def zeros : run Stream Nat :=
  unfold 0 (λ (_ : Nat) → (0, 0))
```

(`examples/zeros.muro`.) Head is `0`. The next seed is `0` again. `head-zeros` is `{head zeros ≡ 0 : Nat}` by `refl`.

### natsFrom

```
def natsFrom : run Π (n : Nat) → Stream Nat :=
  λ (n : Nat) →
    unfold n (λ (+ k : Nat) → (k, suc k))
```

(`examples/nats.muro`.) Each step reuses `k` because `Nat` is Data.

```
{:ok, src} = Muro.emit_file("examples/nats.muro", Muro.Nats)
Code.eval_string(src)
Muro.Nats.natsFrom(0) |> Stream.take(3) |> Enum.to_list()
# [0, {:suc, 0}, {:suc, {:suc, 0}}]
```

Emit of a checked run Stream is `Stream.unfold/2`. The pair is `{head, next_seed}`. `uncons` becomes two replayable views (`Enum.take/2` and `Stream.drop/2`); affinity was already checked.

## Always

`Always A P s` is the coinductive family “`P` holds at every head of `s`.” It is indexed by the stream. `uncons` of a proof `p : Always A P s` has type `P (head s) × Always A P (tail s)`, so `head p : P (head s)` and `tail p : Always A P (tail s)`.

An `unfold` into `Always A P s` takes the current stream `t` and an invariant `x : I`:

```
unfold seed (λ (t : Stream A) → λ (x : I) → (p, next_seed))
```

`I` is a type that may mention `t`. The seed has type `I` at `s`. The body is checked with `t` a variable: `p` proves `P (head t)` and `next_seed` has type `I` at `tail t`. `t` may not be `+`.

When the obligation does not mention the stream, `I` can be `Unit`:

```
def zeros-always-zero : evidence Always Nat (λ (_ : Nat) → {0 ≡ 0 : Nat}) zeros :=
  unfold tt (λ (t : Stream Nat) → λ (_ : Unit) → (refl, tt))
```

When it does, a `Unit` invariant would have to prove `P (head t)` for every stream `t`. The invariant says which stream `t` is instead, and `rewrite` reads the head and the tail off it:

```
def zeros-all-zero : evidence Always Nat IsZero zeros :=
  unfold refl (λ (t : Stream Nat) → λ (e : {t ≡ zeros : Stream Nat}) →
    (rewrite e motive (λ x → IsZero (head x)) in refl,
     rewrite e motive (λ x → {tail x ≡ zeros : Stream Nat}) in refl))
```

(`examples/always.muro`.) The same proof for `natsFrom 0` is refused: its head is `0`, but the invariant at the tail would need `tail (natsFrom 0) ≡ natsFrom 0`. In the other direction, `head (tail p)` for `p : Always Nat IsZero (natsFrom 0)` has type `{suc(0) ≡ 0 : Nat}`, so such a `p` gives `Empty`.

Surface: `Always A P s`. This is evidence. It is omitted at emit.

## Bisimulation

`σ ~ τ` (ASCII `bisim σ τ`) relates two streams of the same type `Stream A`: heads equal, tails related. `uncons` of a proof has type `{head σ ≡ head τ : A} × (tail σ ~ tail τ)`. After J.J.M.M. Rutten, *Elements of Stream Calculus*, ENTCS 45 (2001), Theorem 2.1.

An `unfold` into `σ ~ τ` takes both current streams and an invariant over them:

```
unfold seed (λ (a : Stream A) → λ (b : Stream A) → λ (x : I) → (e, next_seed))
```

The seed has type `I` at `σ, τ`. `e` proves `{head a ≡ head b : A}` and `next_seed` has type `I` at `tail a, tail b`. The invariant `{a ≡ b : Stream A}` proves that convertible streams are bisimilar:

```
def zeros-bisim : evidence zeros ~ zeros' :=
  unfold refl (λ (a : Stream Nat) → λ (b : Stream Nat) → λ (e : {a ≡ b : Stream Nat}) →
    (rewrite e motive (λ x → {head x ≡ head b : Nat}) in refl,
     rewrite e motive (λ x → {tail x ≡ tail b : Stream Nat}) in refl))
```

`nats-tail-bisim : Π (n : Nat) → tail (natsFrom n) ~ natsFrom (suc n)` is the same step under `λ (n : Nat)`. `natsFrom 0 ~ zeros` is refused: with `{a ≡ b}` the seed needs `natsFrom 0 ≡ zeros`, and with `Unit` the step needs equal heads for every two streams.

(`examples/bisim.muro`.) Always, `~`, and their inhabitants are evidence (or live in evidence). They are not Elixir streams.

There are no user-defined ν-predicates. See [Limits](limits.md).

Next: [Either and Dec](either.md).
