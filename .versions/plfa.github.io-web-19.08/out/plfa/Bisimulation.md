---
src       : "src/plfa/Bisimulation.lagda.md"
title     : "Bisimulation: Relating reduction systems"
layout    : page
prev      : /More/
permalink : /Bisimulation/
next      : /Inference/
---

{% raw %}<pre class="Agda"><a id="156" class="Keyword">module</a> <a id="163" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}" class="Module">plfa.Bisimulation</a> <a id="181" class="Keyword">where</a>
</pre>{% endraw %}
Some constructs can be defined in terms of other constructs.  In the
previous chapter, we saw how _let_ terms can be rewritten as an
application of an abstraction, and how two alternative formulations of
products — one with projections and one with case — can be formulated
in terms of each other.  In this chapter, we look at how to formalise
such claims.

Given two different systems, with different terms and reduction rules,
we define what it means to claim that one _simulates_ the other.
Let's call our two systems _source_ and _target_.  Let `M`, `N` range
over terms of the source, and `M†`, `N†` range over terms of the
target.  We define a relation

    M ~ M†

between corresponding terms of the two systems. We have a
_simulation_ of the source by the target if every reduction
in the source has a corresponding reduction sequence
in the target:

_Simulation_: For every `M`, `M†`, and `N`:
If `M ~ M†` and `M —→ N`
then `M† —↠ N†` and `N ~ N†`
for some `N†`.

Or, in a diagram:

    M  --- —→ --- N
    |             |
    |             |
    ~             ~
    |             |
    |             |
    M† --- —↠ --- N†

Sometimes we will have a stronger condition, where each reduction in the source
corresponds to a reduction (rather than a reduction sequence)
in the target:

    M  --- —→ --- N
    |             |
    |             |
    ~             ~
    |             |
    |             |
    M† --- —→ --- N†

This stronger condition is known as _lock-step_ or _on the nose_ simulation.

We are particularly interested in the situation where there is also
a simulation from the target to the source: every reduction in the
target has a corresponding reduction sequence in the source.  This
situation is called a _bisimulation_.

Simulation is established by case analysis over all possible
reductions and all possible terms to which they are related.  For each
reduction step in the source we must show a corresponding reduction
sequence in the target.

For instance, the source might be lambda calculus with _let_
added, and the target the same system with `let` translated out.
The key rule defining our relation will be:

    M ~ M†
    N ~ N†
    --------------------------------
    let x = M in N ~ (ƛ x ⇒ N†) · M†

All the other rules are congruences: variables relate to
themselves, and abstractions and applications relate if their
components relate:

    -----
    x ~ x

    N ~ N†
    ------------------
    ƛ x ⇒ N ~ ƛ x ⇒ N†

    L ~ L†
    M ~ M†
    ---------------
    L · M ~ L† · M†

Covering the other constructs of our language — naturals,
fixpoints, products, and so on — would add little save length.

In this case, our relation can be specified by a function
from source to target:

    (x) †               =  x
    (ƛ x ⇒ N) †         =  ƛ x ⇒ (N †)
    (L · M) †           =  (L †) · (M †)
    (let x = M in N) †  =  (ƛ x ⇒ (N †)) · (M †)

And we have

    M † ≡ N
    -------
    M ~ N

and conversely. But in general we may have a relation without any
corresponding function.

This chapter formalises establishing that `~` as defined
above is a simulation from source to target.  We leave
establishing it in the reverse direction as an exercise.
Another exercise is to show the alternative formulations
of products in
Chapter [More]({{ site.baseurl }}/More/)
are in bisimulation.


## Imports

We import our source language from
Chapter [More]({{ site.baseurl }}/More/):
{% raw %}<pre class="Agda"><a id="3619" class="Keyword">open</a> <a id="3624" class="Keyword">import</a> <a id="3631" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}" class="Module">plfa.More</a>
</pre>{% endraw %}

## Simulation

The simulation is a straightforward formalisation of the rules
in the introduction:
{% raw %}<pre class="Agda"><a id="3750" class="Keyword">infix</a>  <a id="3757" class="Number">4</a> <a id="3759" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3796" class="Datatype Operator">_~_</a>
<a id="3763" class="Keyword">infix</a>  <a id="3770" class="Number">5</a> <a id="3772" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3903" class="InductiveConstructor Operator">~ƛ_</a>
<a id="3776" class="Keyword">infix</a>  <a id="3783" class="Number">7</a> <a id="3785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3988" class="InductiveConstructor Operator">_~·_</a>

<a id="3791" class="Keyword">data</a> <a id="_~_"></a><a id="3796" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3796" class="Datatype Operator">_~_</a> <a id="3800" class="Symbol">:</a> <a id="3802" class="Symbol">∀</a> <a id="3804" class="Symbol">{</a><a id="3805" href="plfa.Bisimulation.html#3805" class="Bound">Γ</a> <a id="3807" href="plfa.Bisimulation.html#3807" class="Bound">A</a><a id="3808" class="Symbol">}</a> <a id="3810" class="Symbol">→</a> <a id="3812" class="Symbol">(</a><a id="3813" href="plfa.Bisimulation.html#3805" class="Bound">Γ</a> <a id="3815" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14947" class="Datatype Operator">⊢</a> <a id="3817" href="plfa.Bisimulation.html#3807" class="Bound">A</a><a id="3818" class="Symbol">)</a> <a id="3820" class="Symbol">→</a> <a id="3822" class="Symbol">(</a><a id="3823" href="plfa.Bisimulation.html#3805" class="Bound">Γ</a> <a id="3825" href="plfa.More.html#14947" class="Datatype Operator">⊢</a> <a id="3827" href="plfa.Bisimulation.html#3807" class="Bound">A</a><a id="3828" class="Symbol">)</a> <a id="3830" class="Symbol">→</a> <a id="3832" class="PrimitiveType">Set</a> <a id="3836" class="Keyword">where</a>

  <a id="_~_.~`"></a><a id="3845" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3845" class="InductiveConstructor">~`</a> <a id="3848" class="Symbol">:</a> <a id="3850" class="Symbol">∀</a> <a id="3852" class="Symbol">{</a><a id="3853" href="plfa.Bisimulation.html#3853" class="Bound">Γ</a> <a id="3855" href="plfa.Bisimulation.html#3855" class="Bound">A</a><a id="3856" class="Symbol">}</a> <a id="3858" class="Symbol">{</a><a id="3859" href="plfa.Bisimulation.html#3859" class="Bound">x</a> <a id="3861" class="Symbol">:</a> <a id="3863" href="plfa.Bisimulation.html#3853" class="Bound">Γ</a> <a id="3865" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14756" class="Datatype Operator">∋</a> <a id="3867" href="plfa.Bisimulation.html#3855" class="Bound">A</a><a id="3868" class="Symbol">}</a>
     <a id="3875" class="Comment">---------</a>
   <a id="3888" class="Symbol">→</a> <a id="3890" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14999" class="InductiveConstructor Operator">`</a> <a id="3892" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3859" class="Bound">x</a> <a id="3894" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="3896" href="plfa.More.html#14999" class="InductiveConstructor Operator">`</a> <a id="3898" href="plfa.Bisimulation.html#3859" class="Bound">x</a>

  <a id="_~_.~ƛ_"></a><a id="3903" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3903" class="InductiveConstructor Operator">~ƛ_</a> <a id="3907" class="Symbol">:</a> <a id="3909" class="Symbol">∀</a> <a id="3911" class="Symbol">{</a><a id="3912" href="plfa.Bisimulation.html#3912" class="Bound">Γ</a> <a id="3914" href="plfa.Bisimulation.html#3914" class="Bound">A</a> <a id="3916" href="plfa.Bisimulation.html#3916" class="Bound">B</a><a id="3917" class="Symbol">}</a> <a id="3919" class="Symbol">{</a><a id="3920" href="plfa.Bisimulation.html#3920" class="Bound">N</a> <a id="3922" href="plfa.Bisimulation.html#3922" class="Bound">N†</a> <a id="3925" class="Symbol">:</a> <a id="3927" href="plfa.Bisimulation.html#3912" class="Bound">Γ</a> <a id="3929" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14672" class="InductiveConstructor Operator">,</a> <a id="3931" href="plfa.Bisimulation.html#3914" class="Bound">A</a> <a id="3933" href="plfa.More.html#14947" class="Datatype Operator">⊢</a> <a id="3935" href="plfa.Bisimulation.html#3916" class="Bound">B</a><a id="3936" class="Symbol">}</a>
    <a id="3942" class="Symbol">→</a> <a id="3944" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3920" class="Bound">N</a> <a id="3946" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="3948" href="plfa.Bisimulation.html#3922" class="Bound">N†</a>
      <a id="3957" class="Comment">----------</a>
    <a id="3972" class="Symbol">→</a> <a id="3974" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#15067" class="InductiveConstructor Operator">ƛ</a> <a id="3976" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3920" class="Bound">N</a> <a id="3978" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="3980" href="plfa.More.html#15067" class="InductiveConstructor Operator">ƛ</a> <a id="3982" href="plfa.Bisimulation.html#3922" class="Bound">N†</a>

  <a id="_~_._~·_"></a><a id="3988" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3988" class="InductiveConstructor Operator">_~·_</a> <a id="3993" class="Symbol">:</a> <a id="3995" class="Symbol">∀</a> <a id="3997" class="Symbol">{</a><a id="3998" href="plfa.Bisimulation.html#3998" class="Bound">Γ</a> <a id="4000" href="plfa.Bisimulation.html#4000" class="Bound">A</a> <a id="4002" href="plfa.Bisimulation.html#4002" class="Bound">B</a><a id="4003" class="Symbol">}</a> <a id="4005" class="Symbol">{</a><a id="4006" href="plfa.Bisimulation.html#4006" class="Bound">L</a> <a id="4008" href="plfa.Bisimulation.html#4008" class="Bound">L†</a> <a id="4011" class="Symbol">:</a> <a id="4013" href="plfa.Bisimulation.html#3998" class="Bound">Γ</a> <a id="4015" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14947" class="Datatype Operator">⊢</a> <a id="4017" href="plfa.Bisimulation.html#4000" class="Bound">A</a> <a id="4019" href="plfa.More.html#14535" class="InductiveConstructor Operator">⇒</a> <a id="4021" href="plfa.Bisimulation.html#4002" class="Bound">B</a><a id="4022" class="Symbol">}</a> <a id="4024" class="Symbol">{</a><a id="4025" href="plfa.Bisimulation.html#4025" class="Bound">M</a> <a id="4027" href="plfa.Bisimulation.html#4027" class="Bound">M†</a> <a id="4030" class="Symbol">:</a> <a id="4032" href="plfa.Bisimulation.html#3998" class="Bound">Γ</a> <a id="4034" href="plfa.More.html#14947" class="Datatype Operator">⊢</a> <a id="4036" href="plfa.Bisimulation.html#4000" class="Bound">A</a><a id="4037" class="Symbol">}</a>
    <a id="4043" class="Symbol">→</a> <a id="4045" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4006" class="Bound">L</a> <a id="4047" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="4049" href="plfa.Bisimulation.html#4008" class="Bound">L†</a>
    <a id="4056" class="Symbol">→</a> <a id="4058" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4025" class="Bound">M</a> <a id="4060" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="4062" href="plfa.Bisimulation.html#4027" class="Bound">M†</a>
      <a id="4071" class="Comment">---------------</a>
    <a id="4091" class="Symbol">→</a> <a id="4093" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4006" class="Bound">L</a> <a id="4095" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#15135" class="InductiveConstructor Operator">·</a> <a id="4097" href="plfa.Bisimulation.html#4025" class="Bound">M</a> <a id="4099" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="4101" href="plfa.Bisimulation.html#4008" class="Bound">L†</a> <a id="4104" href="plfa.More.html#15135" class="InductiveConstructor Operator">·</a> <a id="4106" href="plfa.Bisimulation.html#4027" class="Bound">M†</a>

  <a id="_~_.~let"></a><a id="4112" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4112" class="InductiveConstructor">~let</a> <a id="4117" class="Symbol">:</a> <a id="4119" class="Symbol">∀</a> <a id="4121" class="Symbol">{</a><a id="4122" href="plfa.Bisimulation.html#4122" class="Bound">Γ</a> <a id="4124" href="plfa.Bisimulation.html#4124" class="Bound">A</a> <a id="4126" href="plfa.Bisimulation.html#4126" class="Bound">B</a><a id="4127" class="Symbol">}</a> <a id="4129" class="Symbol">{</a><a id="4130" href="plfa.Bisimulation.html#4130" class="Bound">M</a> <a id="4132" href="plfa.Bisimulation.html#4132" class="Bound">M†</a> <a id="4135" class="Symbol">:</a> <a id="4137" href="plfa.Bisimulation.html#4122" class="Bound">Γ</a> <a id="4139" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14947" class="Datatype Operator">⊢</a> <a id="4141" href="plfa.Bisimulation.html#4124" class="Bound">A</a><a id="4142" class="Symbol">}</a> <a id="4144" class="Symbol">{</a><a id="4145" href="plfa.Bisimulation.html#4145" class="Bound">N</a> <a id="4147" href="plfa.Bisimulation.html#4147" class="Bound">N†</a> <a id="4150" class="Symbol">:</a> <a id="4152" href="plfa.Bisimulation.html#4122" class="Bound">Γ</a> <a id="4154" href="plfa.More.html#14672" class="InductiveConstructor Operator">,</a> <a id="4156" href="plfa.Bisimulation.html#4124" class="Bound">A</a> <a id="4158" href="plfa.More.html#14947" class="Datatype Operator">⊢</a> <a id="4160" href="plfa.Bisimulation.html#4126" class="Bound">B</a><a id="4161" class="Symbol">}</a>
    <a id="4167" class="Symbol">→</a> <a id="4169" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4130" class="Bound">M</a> <a id="4171" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="4173" href="plfa.Bisimulation.html#4132" class="Bound">M†</a>
    <a id="4180" class="Symbol">→</a> <a id="4182" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4145" class="Bound">N</a> <a id="4184" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="4186" href="plfa.Bisimulation.html#4147" class="Bound">N†</a>
      <a id="4195" class="Comment">----------------------</a>
    <a id="4222" class="Symbol">→</a> <a id="4224" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#15641" class="InductiveConstructor">`let</a> <a id="4229" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4130" class="Bound">M</a> <a id="4231" href="plfa.Bisimulation.html#4145" class="Bound">N</a> <a id="4233" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="4235" class="Symbol">(</a><a id="4236" href="plfa.More.html#15067" class="InductiveConstructor Operator">ƛ</a> <a id="4238" href="plfa.Bisimulation.html#4147" class="Bound">N†</a><a id="4240" class="Symbol">)</a> <a id="4242" href="plfa.More.html#15135" class="InductiveConstructor Operator">·</a> <a id="4244" href="plfa.Bisimulation.html#4132" class="Bound">M†</a>
</pre>{% endraw %}The language in Chapter [More]({{ site.baseurl }}/More/) has more constructs, which we could easily add.
However, leaving the simulation small let's us focus on the essence.
It's a handy technical trick that we can have a large source language,
but only bother to include in the simulation the terms of interest.

#### Exercise `_†`

Formalise the translation from source to target given in the introduction.
Show that `M † ≡ N` implies `M ~ N`, and conversely.

{% raw %}<pre class="Agda"><a id="4718" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Simulation commutes with values

We need a number of technical results. The first is that simulation
commutes with values.  That is, if `M ~ M†` and `M` is a value then
`M†` is also a value:
{% raw %}<pre class="Agda"><a id="~val"></a><a id="4945" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4945" class="Function">~val</a> <a id="4950" class="Symbol">:</a> <a id="4952" class="Symbol">∀</a> <a id="4954" class="Symbol">{</a><a id="4955" href="plfa.Bisimulation.html#4955" class="Bound">Γ</a> <a id="4957" href="plfa.Bisimulation.html#4957" class="Bound">A</a><a id="4958" class="Symbol">}</a> <a id="4960" class="Symbol">{</a><a id="4961" href="plfa.Bisimulation.html#4961" class="Bound">M</a> <a id="4963" href="plfa.Bisimulation.html#4963" class="Bound">M†</a> <a id="4966" class="Symbol">:</a> <a id="4968" href="plfa.Bisimulation.html#4955" class="Bound">Γ</a> <a id="4970" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14947" class="Datatype Operator">⊢</a> <a id="4972" href="plfa.Bisimulation.html#4957" class="Bound">A</a><a id="4973" class="Symbol">}</a>
  <a id="4977" class="Symbol">→</a> <a id="4979" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4961" class="Bound">M</a> <a id="4981" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="4983" href="plfa.Bisimulation.html#4963" class="Bound">M†</a>
  <a id="4988" class="Symbol">→</a> <a id="4990" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#18886" class="Datatype">Value</a> <a id="4996" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4961" class="Bound">M</a>
    <a id="5002" class="Comment">--------</a>
  <a id="5013" class="Symbol">→</a> <a id="5015" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#18886" class="Datatype">Value</a> <a id="5021" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4963" class="Bound">M†</a>
<a id="5024" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4945" class="Function">~val</a> <a id="5029" href="plfa.Bisimulation.html#3845" class="InductiveConstructor">~`</a>           <a id="5042" class="Symbol">()</a>
<a id="5045" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4945" class="Function">~val</a> <a id="5050" class="Symbol">(</a><a id="5051" href="plfa.Bisimulation.html#3903" class="InductiveConstructor Operator">~ƛ</a> <a id="5054" href="plfa.Bisimulation.html#5054" class="Bound">~N</a><a id="5056" class="Symbol">)</a>      <a id="5063" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#18941" class="InductiveConstructor">V-ƛ</a>  <a id="5068" class="Symbol">=</a>  <a id="5071" href="plfa.More.html#18941" class="InductiveConstructor">V-ƛ</a>
<a id="5075" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4945" class="Function">~val</a> <a id="5080" class="Symbol">(</a><a id="5081" href="plfa.Bisimulation.html#5081" class="Bound">~L</a> <a id="5084" href="plfa.Bisimulation.html#3988" class="InductiveConstructor Operator">~·</a> <a id="5087" href="plfa.Bisimulation.html#5087" class="Bound">~M</a><a id="5089" class="Symbol">)</a>   <a id="5093" class="Symbol">()</a>
<a id="5096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4945" class="Function">~val</a> <a id="5101" class="Symbol">(</a><a id="5102" href="plfa.Bisimulation.html#4112" class="InductiveConstructor">~let</a> <a id="5107" href="plfa.Bisimulation.html#5107" class="Bound">~M</a> <a id="5110" href="plfa.Bisimulation.html#5110" class="Bound">~N</a><a id="5112" class="Symbol">)</a> <a id="5114" class="Symbol">()</a>
</pre>{% endraw %}It is a straightforward case analysis, where here the only value
of interest is a lambda abstraction.

#### Exercise `~val⁻¹`

Show that this also holds in the reverse direction: if `M ~ M†`
and `Value M†` then `Value M`.

{% raw %}<pre class="Agda"><a id="5348" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Simulation commutes with renaming

The next technical result is that simulation commutes with renaming.
That is, if `ρ` maps any judgment `Γ ∋ A` to a judgment `Δ ∋ A`,
and if `M ~ M†` then `rename ρ M ~ rename ρ M†`:

{% raw %}<pre class="Agda"><a id="~rename"></a><a id="5603" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#5603" class="Function">~rename</a> <a id="5611" class="Symbol">:</a> <a id="5613" class="Symbol">∀</a> <a id="5615" class="Symbol">{</a><a id="5616" href="plfa.Bisimulation.html#5616" class="Bound">Γ</a> <a id="5618" href="plfa.Bisimulation.html#5618" class="Bound">Δ</a><a id="5619" class="Symbol">}</a>
  <a id="5623" class="Symbol">→</a> <a id="5625" class="Symbol">(</a><a id="5626" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#5626" class="Bound">ρ</a> <a id="5628" class="Symbol">:</a> <a id="5630" class="Symbol">∀</a> <a id="5632" class="Symbol">{</a><a id="5633" href="plfa.Bisimulation.html#5633" class="Bound">A</a><a id="5634" class="Symbol">}</a> <a id="5636" class="Symbol">→</a> <a id="5638" href="plfa.Bisimulation.html#5616" class="Bound">Γ</a> <a id="5640" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14756" class="Datatype Operator">∋</a> <a id="5642" href="plfa.Bisimulation.html#5633" class="Bound">A</a> <a id="5644" class="Symbol">→</a> <a id="5646" href="plfa.Bisimulation.html#5618" class="Bound">Δ</a> <a id="5648" href="plfa.More.html#14756" class="Datatype Operator">∋</a> <a id="5650" href="plfa.Bisimulation.html#5633" class="Bound">A</a><a id="5651" class="Symbol">)</a>
    <a id="5657" class="Comment">----------------------------------------------------------</a>
  <a id="5718" class="Symbol">→</a> <a id="5720" class="Symbol">(∀</a> <a id="5723" class="Symbol">{</a><a id="5724" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#5724" class="Bound">A</a><a id="5725" class="Symbol">}</a> <a id="5727" class="Symbol">{</a><a id="5728" href="plfa.Bisimulation.html#5728" class="Bound">M</a> <a id="5730" href="plfa.Bisimulation.html#5730" class="Bound">M†</a> <a id="5733" class="Symbol">:</a> <a id="5735" href="plfa.Bisimulation.html#5616" class="Bound">Γ</a> <a id="5737" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14947" class="Datatype Operator">⊢</a> <a id="5739" href="plfa.Bisimulation.html#5724" class="Bound">A</a><a id="5740" class="Symbol">}</a> <a id="5742" class="Symbol">→</a> <a id="5744" href="plfa.Bisimulation.html#5728" class="Bound">M</a> <a id="5746" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="5748" href="plfa.Bisimulation.html#5730" class="Bound">M†</a> <a id="5751" class="Symbol">→</a> <a id="5753" href="plfa.More.html#16686" class="Function">rename</a> <a id="5760" href="plfa.Bisimulation.html#5626" class="Bound">ρ</a> <a id="5762" href="plfa.Bisimulation.html#5728" class="Bound">M</a> <a id="5764" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="5766" href="plfa.More.html#16686" class="Function">rename</a> <a id="5773" href="plfa.Bisimulation.html#5626" class="Bound">ρ</a> <a id="5775" href="plfa.Bisimulation.html#5730" class="Bound">M†</a><a id="5777" class="Symbol">)</a>
<a id="5779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#5603" class="Function">~rename</a> <a id="5787" href="plfa.Bisimulation.html#5787" class="Bound">ρ</a> <a id="5789" class="Symbol">(</a><a id="5790" href="plfa.Bisimulation.html#3845" class="InductiveConstructor">~`</a><a id="5792" class="Symbol">)</a>          <a id="5803" class="Symbol">=</a>  <a id="5806" href="plfa.Bisimulation.html#3845" class="InductiveConstructor">~`</a>
<a id="5809" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#5603" class="Function">~rename</a> <a id="5817" href="plfa.Bisimulation.html#5817" class="Bound">ρ</a> <a id="5819" class="Symbol">(</a><a id="5820" href="plfa.Bisimulation.html#3903" class="InductiveConstructor Operator">~ƛ</a> <a id="5823" href="plfa.Bisimulation.html#5823" class="Bound">~N</a><a id="5825" class="Symbol">)</a>       <a id="5833" class="Symbol">=</a>  <a id="5836" href="plfa.Bisimulation.html#3903" class="InductiveConstructor Operator">~ƛ</a> <a id="5839" class="Symbol">(</a><a id="5840" href="plfa.Bisimulation.html#5603" class="Function">~rename</a> <a id="5848" class="Symbol">(</a><a id="5849" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#16567" class="Function">ext</a> <a id="5853" href="plfa.Bisimulation.html#5817" class="Bound">ρ</a><a id="5854" class="Symbol">)</a> <a id="5856" href="plfa.Bisimulation.html#5823" class="Bound">~N</a><a id="5858" class="Symbol">)</a>
<a id="5860" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#5603" class="Function">~rename</a> <a id="5868" href="plfa.Bisimulation.html#5868" class="Bound">ρ</a> <a id="5870" class="Symbol">(</a><a id="5871" href="plfa.Bisimulation.html#5871" class="Bound">~L</a> <a id="5874" href="plfa.Bisimulation.html#3988" class="InductiveConstructor Operator">~·</a> <a id="5877" href="plfa.Bisimulation.html#5877" class="Bound">~M</a><a id="5879" class="Symbol">)</a>    <a id="5884" class="Symbol">=</a>  <a id="5887" class="Symbol">(</a><a id="5888" href="plfa.Bisimulation.html#5603" class="Function">~rename</a> <a id="5896" href="plfa.Bisimulation.html#5868" class="Bound">ρ</a> <a id="5898" href="plfa.Bisimulation.html#5871" class="Bound">~L</a><a id="5900" class="Symbol">)</a> <a id="5902" href="plfa.Bisimulation.html#3988" class="InductiveConstructor Operator">~·</a> <a id="5905" class="Symbol">(</a><a id="5906" href="plfa.Bisimulation.html#5603" class="Function">~rename</a> <a id="5914" href="plfa.Bisimulation.html#5868" class="Bound">ρ</a> <a id="5916" href="plfa.Bisimulation.html#5877" class="Bound">~M</a><a id="5918" class="Symbol">)</a>
<a id="5920" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#5603" class="Function">~rename</a> <a id="5928" href="plfa.Bisimulation.html#5928" class="Bound">ρ</a> <a id="5930" class="Symbol">(</a><a id="5931" href="plfa.Bisimulation.html#4112" class="InductiveConstructor">~let</a> <a id="5936" href="plfa.Bisimulation.html#5936" class="Bound">~M</a> <a id="5939" href="plfa.Bisimulation.html#5939" class="Bound">~N</a><a id="5941" class="Symbol">)</a>  <a id="5944" class="Symbol">=</a>  <a id="5947" href="plfa.Bisimulation.html#4112" class="InductiveConstructor">~let</a> <a id="5952" class="Symbol">(</a><a id="5953" href="plfa.Bisimulation.html#5603" class="Function">~rename</a> <a id="5961" href="plfa.Bisimulation.html#5928" class="Bound">ρ</a> <a id="5963" href="plfa.Bisimulation.html#5936" class="Bound">~M</a><a id="5965" class="Symbol">)</a> <a id="5967" class="Symbol">(</a><a id="5968" href="plfa.Bisimulation.html#5603" class="Function">~rename</a> <a id="5976" class="Symbol">(</a><a id="5977" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#16567" class="Function">ext</a> <a id="5981" href="plfa.Bisimulation.html#5928" class="Bound">ρ</a><a id="5982" class="Symbol">)</a> <a id="5984" href="plfa.Bisimulation.html#5939" class="Bound">~N</a><a id="5986" class="Symbol">)</a>
</pre>{% endraw %}The structure of the proof is similar to the structure of renaming itself:
reconstruct each term with recursive invocation, extending the environment
where appropriate (in this case, only for the body of an abstraction).


## Simulation commutes with substitution

The third technical result is that simulation commutes with substitution.
It is more complex than renaming, because where we had one renaming map
`ρ` here we need two substitution maps, `σ` and `σ†`.

The proof first requires we establish an analogue of extension.
If `σ` and `σ†` both map any judgment `Γ ∋ A` to a judgment `Δ ⊢ A`,
such that for every `x` in `Γ ∋ A` we have `σ x ~ σ† x`,
then for any `x` in `Γ , B ∋ A` we have `exts σ x ~ exts σ† x`:
{% raw %}<pre class="Agda"><a id="~exts"></a><a id="6716" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#6716" class="Function">~exts</a> <a id="6722" class="Symbol">:</a> <a id="6724" class="Symbol">∀</a> <a id="6726" class="Symbol">{</a><a id="6727" href="plfa.Bisimulation.html#6727" class="Bound">Γ</a> <a id="6729" href="plfa.Bisimulation.html#6729" class="Bound">Δ</a><a id="6730" class="Symbol">}</a>
  <a id="6734" class="Symbol">→</a> <a id="6736" class="Symbol">{</a><a id="6737" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#6737" class="Bound">σ</a>  <a id="6740" class="Symbol">:</a> <a id="6742" class="Symbol">∀</a> <a id="6744" class="Symbol">{</a><a id="6745" href="plfa.Bisimulation.html#6745" class="Bound">A</a><a id="6746" class="Symbol">}</a> <a id="6748" class="Symbol">→</a> <a id="6750" href="plfa.Bisimulation.html#6727" class="Bound">Γ</a> <a id="6752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14756" class="Datatype Operator">∋</a> <a id="6754" href="plfa.Bisimulation.html#6745" class="Bound">A</a> <a id="6756" class="Symbol">→</a> <a id="6758" href="plfa.Bisimulation.html#6729" class="Bound">Δ</a> <a id="6760" href="plfa.More.html#14947" class="Datatype Operator">⊢</a> <a id="6762" href="plfa.Bisimulation.html#6745" class="Bound">A</a><a id="6763" class="Symbol">}</a>
  <a id="6767" class="Symbol">→</a> <a id="6769" class="Symbol">{</a><a id="6770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#6770" class="Bound">σ†</a> <a id="6773" class="Symbol">:</a> <a id="6775" class="Symbol">∀</a> <a id="6777" class="Symbol">{</a><a id="6778" href="plfa.Bisimulation.html#6778" class="Bound">A</a><a id="6779" class="Symbol">}</a> <a id="6781" class="Symbol">→</a> <a id="6783" href="plfa.Bisimulation.html#6727" class="Bound">Γ</a> <a id="6785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14756" class="Datatype Operator">∋</a> <a id="6787" href="plfa.Bisimulation.html#6778" class="Bound">A</a> <a id="6789" class="Symbol">→</a> <a id="6791" href="plfa.Bisimulation.html#6729" class="Bound">Δ</a> <a id="6793" href="plfa.More.html#14947" class="Datatype Operator">⊢</a> <a id="6795" href="plfa.Bisimulation.html#6778" class="Bound">A</a><a id="6796" class="Symbol">}</a>
  <a id="6800" class="Symbol">→</a> <a id="6802" class="Symbol">(∀</a> <a id="6805" class="Symbol">{</a><a id="6806" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#6806" class="Bound">A</a><a id="6807" class="Symbol">}</a> <a id="6809" class="Symbol">→</a> <a id="6811" class="Symbol">(</a><a id="6812" href="plfa.Bisimulation.html#6812" class="Bound">x</a> <a id="6814" class="Symbol">:</a> <a id="6816" href="plfa.Bisimulation.html#6727" class="Bound">Γ</a> <a id="6818" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14756" class="Datatype Operator">∋</a> <a id="6820" href="plfa.Bisimulation.html#6806" class="Bound">A</a><a id="6821" class="Symbol">)</a> <a id="6823" class="Symbol">→</a> <a id="6825" href="plfa.Bisimulation.html#6737" class="Bound">σ</a> <a id="6827" href="plfa.Bisimulation.html#6812" class="Bound">x</a> <a id="6829" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="6831" href="plfa.Bisimulation.html#6770" class="Bound">σ†</a> <a id="6834" href="plfa.Bisimulation.html#6812" class="Bound">x</a><a id="6835" class="Symbol">)</a>
    <a id="6841" class="Comment">--------------------------------------------------</a>
  <a id="6894" class="Symbol">→</a> <a id="6896" class="Symbol">(∀</a> <a id="6899" class="Symbol">{</a><a id="6900" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#6900" class="Bound">A</a> <a id="6902" href="plfa.Bisimulation.html#6902" class="Bound">B</a><a id="6903" class="Symbol">}</a> <a id="6905" class="Symbol">→</a> <a id="6907" class="Symbol">(</a><a id="6908" href="plfa.Bisimulation.html#6908" class="Bound">x</a> <a id="6910" class="Symbol">:</a> <a id="6912" href="plfa.Bisimulation.html#6727" class="Bound">Γ</a> <a id="6914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14672" class="InductiveConstructor Operator">,</a> <a id="6916" href="plfa.Bisimulation.html#6902" class="Bound">B</a> <a id="6918" href="plfa.More.html#14756" class="Datatype Operator">∋</a> <a id="6920" href="plfa.Bisimulation.html#6900" class="Bound">A</a><a id="6921" class="Symbol">)</a> <a id="6923" class="Symbol">→</a> <a id="6925" href="plfa.More.html#17505" class="Function">exts</a> <a id="6930" href="plfa.Bisimulation.html#6737" class="Bound">σ</a> <a id="6932" href="plfa.Bisimulation.html#6908" class="Bound">x</a> <a id="6934" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="6936" href="plfa.More.html#17505" class="Function">exts</a> <a id="6941" href="plfa.Bisimulation.html#6770" class="Bound">σ†</a> <a id="6944" href="plfa.Bisimulation.html#6908" class="Bound">x</a><a id="6945" class="Symbol">)</a>
<a id="6947" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#6716" class="Function">~exts</a> <a id="6953" href="plfa.Bisimulation.html#6953" class="Bound">~σ</a> <a id="6956" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14792" class="InductiveConstructor">Z</a>      <a id="6963" class="Symbol">=</a>  <a id="6966" href="plfa.Bisimulation.html#3845" class="InductiveConstructor">~`</a>
<a id="6969" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#6716" class="Function">~exts</a> <a id="6975" href="plfa.Bisimulation.html#6975" class="Bound">~σ</a> <a id="6978" class="Symbol">(</a><a id="6979" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14839" class="InductiveConstructor Operator">S</a> <a id="6981" href="plfa.Bisimulation.html#6981" class="Bound">x</a><a id="6982" class="Symbol">)</a>  <a id="6985" class="Symbol">=</a>  <a id="6988" href="plfa.Bisimulation.html#5603" class="Function">~rename</a> <a id="6996" href="plfa.More.html#14839" class="InductiveConstructor Operator">S_</a> <a id="6999" class="Symbol">(</a><a id="7000" href="plfa.Bisimulation.html#6975" class="Bound">~σ</a> <a id="7003" href="plfa.Bisimulation.html#6981" class="Bound">x</a><a id="7004" class="Symbol">)</a>
</pre>{% endraw %}The structure of the proof is similar to the structure of extension itself.
The newly introduced variable trivially relates to itself, and otherwise
we apply renaming to the hypothesis.

With extension under our belts, it is straightforward to show
substitution commutes.  If `σ` and `σ†` both map any judgment `Γ ∋ A`
to a judgment `Δ ⊢ A`, such that for every `x` in `Γ ∋ A` we have `σ
x ~ σ† x`, and if `M ~ M†`, then `subst σ M ~ subst σ† M†`:
{% raw %}<pre class="Agda"><a id="~subst"></a><a id="7462" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#7462" class="Function">~subst</a> <a id="7469" class="Symbol">:</a> <a id="7471" class="Symbol">∀</a> <a id="7473" class="Symbol">{</a><a id="7474" href="plfa.Bisimulation.html#7474" class="Bound">Γ</a> <a id="7476" href="plfa.Bisimulation.html#7476" class="Bound">Δ</a><a id="7477" class="Symbol">}</a>
  <a id="7481" class="Symbol">→</a> <a id="7483" class="Symbol">{</a><a id="7484" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#7484" class="Bound">σ</a>  <a id="7487" class="Symbol">:</a> <a id="7489" class="Symbol">∀</a> <a id="7491" class="Symbol">{</a><a id="7492" href="plfa.Bisimulation.html#7492" class="Bound">A</a><a id="7493" class="Symbol">}</a> <a id="7495" class="Symbol">→</a> <a id="7497" href="plfa.Bisimulation.html#7474" class="Bound">Γ</a> <a id="7499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14756" class="Datatype Operator">∋</a> <a id="7501" href="plfa.Bisimulation.html#7492" class="Bound">A</a> <a id="7503" class="Symbol">→</a> <a id="7505" href="plfa.Bisimulation.html#7476" class="Bound">Δ</a> <a id="7507" href="plfa.More.html#14947" class="Datatype Operator">⊢</a> <a id="7509" href="plfa.Bisimulation.html#7492" class="Bound">A</a><a id="7510" class="Symbol">}</a>
  <a id="7514" class="Symbol">→</a> <a id="7516" class="Symbol">{</a><a id="7517" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#7517" class="Bound">σ†</a> <a id="7520" class="Symbol">:</a> <a id="7522" class="Symbol">∀</a> <a id="7524" class="Symbol">{</a><a id="7525" href="plfa.Bisimulation.html#7525" class="Bound">A</a><a id="7526" class="Symbol">}</a> <a id="7528" class="Symbol">→</a> <a id="7530" href="plfa.Bisimulation.html#7474" class="Bound">Γ</a> <a id="7532" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14756" class="Datatype Operator">∋</a> <a id="7534" href="plfa.Bisimulation.html#7525" class="Bound">A</a> <a id="7536" class="Symbol">→</a> <a id="7538" href="plfa.Bisimulation.html#7476" class="Bound">Δ</a> <a id="7540" href="plfa.More.html#14947" class="Datatype Operator">⊢</a> <a id="7542" href="plfa.Bisimulation.html#7525" class="Bound">A</a><a id="7543" class="Symbol">}</a>
  <a id="7547" class="Symbol">→</a> <a id="7549" class="Symbol">(∀</a> <a id="7552" class="Symbol">{</a><a id="7553" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#7553" class="Bound">A</a><a id="7554" class="Symbol">}</a> <a id="7556" class="Symbol">→</a> <a id="7558" class="Symbol">(</a><a id="7559" href="plfa.Bisimulation.html#7559" class="Bound">x</a> <a id="7561" class="Symbol">:</a> <a id="7563" href="plfa.Bisimulation.html#7474" class="Bound">Γ</a> <a id="7565" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14756" class="Datatype Operator">∋</a> <a id="7567" href="plfa.Bisimulation.html#7553" class="Bound">A</a><a id="7568" class="Symbol">)</a> <a id="7570" class="Symbol">→</a> <a id="7572" href="plfa.Bisimulation.html#7484" class="Bound">σ</a> <a id="7574" href="plfa.Bisimulation.html#7559" class="Bound">x</a> <a id="7576" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="7578" href="plfa.Bisimulation.html#7517" class="Bound">σ†</a> <a id="7581" href="plfa.Bisimulation.html#7559" class="Bound">x</a><a id="7582" class="Symbol">)</a>
    <a id="7588" class="Comment">---------------------------------------------------------</a>
  <a id="7648" class="Symbol">→</a> <a id="7650" class="Symbol">(∀</a> <a id="7653" class="Symbol">{</a><a id="7654" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#7654" class="Bound">A</a><a id="7655" class="Symbol">}</a> <a id="7657" class="Symbol">{</a><a id="7658" href="plfa.Bisimulation.html#7658" class="Bound">M</a> <a id="7660" href="plfa.Bisimulation.html#7660" class="Bound">M†</a> <a id="7663" class="Symbol">:</a> <a id="7665" href="plfa.Bisimulation.html#7474" class="Bound">Γ</a> <a id="7667" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14947" class="Datatype Operator">⊢</a> <a id="7669" href="plfa.Bisimulation.html#7654" class="Bound">A</a><a id="7670" class="Symbol">}</a> <a id="7672" class="Symbol">→</a> <a id="7674" href="plfa.Bisimulation.html#7658" class="Bound">M</a> <a id="7676" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="7678" href="plfa.Bisimulation.html#7660" class="Bound">M†</a> <a id="7681" class="Symbol">→</a> <a id="7683" href="plfa.More.html#17637" class="Function">subst</a> <a id="7689" href="plfa.Bisimulation.html#7484" class="Bound">σ</a> <a id="7691" href="plfa.Bisimulation.html#7658" class="Bound">M</a> <a id="7693" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="7695" href="plfa.More.html#17637" class="Function">subst</a> <a id="7701" href="plfa.Bisimulation.html#7517" class="Bound">σ†</a> <a id="7704" href="plfa.Bisimulation.html#7660" class="Bound">M†</a><a id="7706" class="Symbol">)</a>
<a id="7708" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#7462" class="Function">~subst</a> <a id="7715" href="plfa.Bisimulation.html#7715" class="Bound">~σ</a> <a id="7718" class="Symbol">(</a><a id="7719" href="plfa.Bisimulation.html#3845" class="InductiveConstructor">~`</a> <a id="7722" class="Symbol">{</a><a id="7723" class="Argument">x</a> <a id="7725" class="Symbol">=</a> <a id="7727" href="plfa.Bisimulation.html#7727" class="Bound">x</a><a id="7728" class="Symbol">})</a>  <a id="7732" class="Symbol">=</a>  <a id="7735" href="plfa.Bisimulation.html#7715" class="Bound">~σ</a> <a id="7738" href="plfa.Bisimulation.html#7727" class="Bound">x</a>
<a id="7740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#7462" class="Function">~subst</a> <a id="7747" href="plfa.Bisimulation.html#7747" class="Bound">~σ</a> <a id="7750" class="Symbol">(</a><a id="7751" href="plfa.Bisimulation.html#3903" class="InductiveConstructor Operator">~ƛ</a> <a id="7754" href="plfa.Bisimulation.html#7754" class="Bound">~N</a><a id="7756" class="Symbol">)</a>       <a id="7764" class="Symbol">=</a>  <a id="7767" href="plfa.Bisimulation.html#3903" class="InductiveConstructor Operator">~ƛ</a> <a id="7770" class="Symbol">(</a><a id="7771" href="plfa.Bisimulation.html#7462" class="Function">~subst</a> <a id="7778" class="Symbol">(</a><a id="7779" href="plfa.Bisimulation.html#6716" class="Function">~exts</a> <a id="7785" href="plfa.Bisimulation.html#7747" class="Bound">~σ</a><a id="7787" class="Symbol">)</a> <a id="7789" href="plfa.Bisimulation.html#7754" class="Bound">~N</a><a id="7791" class="Symbol">)</a>
<a id="7793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#7462" class="Function">~subst</a> <a id="7800" href="plfa.Bisimulation.html#7800" class="Bound">~σ</a> <a id="7803" class="Symbol">(</a><a id="7804" href="plfa.Bisimulation.html#7804" class="Bound">~L</a> <a id="7807" href="plfa.Bisimulation.html#3988" class="InductiveConstructor Operator">~·</a> <a id="7810" href="plfa.Bisimulation.html#7810" class="Bound">~M</a><a id="7812" class="Symbol">)</a>    <a id="7817" class="Symbol">=</a>  <a id="7820" class="Symbol">(</a><a id="7821" href="plfa.Bisimulation.html#7462" class="Function">~subst</a> <a id="7828" href="plfa.Bisimulation.html#7800" class="Bound">~σ</a> <a id="7831" href="plfa.Bisimulation.html#7804" class="Bound">~L</a><a id="7833" class="Symbol">)</a> <a id="7835" href="plfa.Bisimulation.html#3988" class="InductiveConstructor Operator">~·</a> <a id="7838" class="Symbol">(</a><a id="7839" href="plfa.Bisimulation.html#7462" class="Function">~subst</a> <a id="7846" href="plfa.Bisimulation.html#7800" class="Bound">~σ</a> <a id="7849" href="plfa.Bisimulation.html#7810" class="Bound">~M</a><a id="7851" class="Symbol">)</a>
<a id="7853" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#7462" class="Function">~subst</a> <a id="7860" href="plfa.Bisimulation.html#7860" class="Bound">~σ</a> <a id="7863" class="Symbol">(</a><a id="7864" href="plfa.Bisimulation.html#4112" class="InductiveConstructor">~let</a> <a id="7869" href="plfa.Bisimulation.html#7869" class="Bound">~M</a> <a id="7872" href="plfa.Bisimulation.html#7872" class="Bound">~N</a><a id="7874" class="Symbol">)</a>  <a id="7877" class="Symbol">=</a>  <a id="7880" href="plfa.Bisimulation.html#4112" class="InductiveConstructor">~let</a> <a id="7885" class="Symbol">(</a><a id="7886" href="plfa.Bisimulation.html#7462" class="Function">~subst</a> <a id="7893" href="plfa.Bisimulation.html#7860" class="Bound">~σ</a> <a id="7896" href="plfa.Bisimulation.html#7869" class="Bound">~M</a><a id="7898" class="Symbol">)</a> <a id="7900" class="Symbol">(</a><a id="7901" href="plfa.Bisimulation.html#7462" class="Function">~subst</a> <a id="7908" class="Symbol">(</a><a id="7909" href="plfa.Bisimulation.html#6716" class="Function">~exts</a> <a id="7915" href="plfa.Bisimulation.html#7860" class="Bound">~σ</a><a id="7917" class="Symbol">)</a> <a id="7919" href="plfa.Bisimulation.html#7872" class="Bound">~N</a><a id="7921" class="Symbol">)</a>
</pre>{% endraw %}Again, the structure of the proof is similar to the structure of
substitution itself: reconstruct each term with recursive invocation,
extending the environment where appropriate (in this case, only for
the body of an abstraction).

From the general case of substitution, it is also easy to derive
the required special case.  If `N ~ N†` and `M ~ M†`, then
`N [ M ] ~ N† [ M† ]`:
{% raw %}<pre class="Agda"><a id="~sub"></a><a id="8311" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#8311" class="Function">~sub</a> <a id="8316" class="Symbol">:</a> <a id="8318" class="Symbol">∀</a> <a id="8320" class="Symbol">{</a><a id="8321" href="plfa.Bisimulation.html#8321" class="Bound">Γ</a> <a id="8323" href="plfa.Bisimulation.html#8323" class="Bound">A</a> <a id="8325" href="plfa.Bisimulation.html#8325" class="Bound">B</a><a id="8326" class="Symbol">}</a> <a id="8328" class="Symbol">{</a><a id="8329" href="plfa.Bisimulation.html#8329" class="Bound">N</a> <a id="8331" href="plfa.Bisimulation.html#8331" class="Bound">N†</a> <a id="8334" class="Symbol">:</a> <a id="8336" href="plfa.Bisimulation.html#8321" class="Bound">Γ</a> <a id="8338" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14672" class="InductiveConstructor Operator">,</a> <a id="8340" href="plfa.Bisimulation.html#8325" class="Bound">B</a> <a id="8342" href="plfa.More.html#14947" class="Datatype Operator">⊢</a> <a id="8344" href="plfa.Bisimulation.html#8323" class="Bound">A</a><a id="8345" class="Symbol">}</a> <a id="8347" class="Symbol">{</a><a id="8348" href="plfa.Bisimulation.html#8348" class="Bound">M</a> <a id="8350" href="plfa.Bisimulation.html#8350" class="Bound">M†</a> <a id="8353" class="Symbol">:</a> <a id="8355" href="plfa.Bisimulation.html#8321" class="Bound">Γ</a> <a id="8357" href="plfa.More.html#14947" class="Datatype Operator">⊢</a> <a id="8359" href="plfa.Bisimulation.html#8325" class="Bound">B</a><a id="8360" class="Symbol">}</a>
  <a id="8364" class="Symbol">→</a> <a id="8366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#8329" class="Bound">N</a> <a id="8368" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="8370" href="plfa.Bisimulation.html#8331" class="Bound">N†</a>
  <a id="8375" class="Symbol">→</a> <a id="8377" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#8348" class="Bound">M</a> <a id="8379" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="8381" href="plfa.Bisimulation.html#8350" class="Bound">M†</a>
    <a id="8388" class="Comment">-----------------------</a>
  <a id="8414" class="Symbol">→</a> <a id="8416" class="Symbol">(</a><a id="8417" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#8329" class="Bound">N</a> <a id="8419" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#18430" class="Function Operator">[</a> <a id="8421" href="plfa.Bisimulation.html#8348" class="Bound">M</a> <a id="8423" href="plfa.More.html#18430" class="Function Operator">]</a><a id="8424" class="Symbol">)</a> <a id="8426" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="8428" class="Symbol">(</a><a id="8429" href="plfa.Bisimulation.html#8331" class="Bound">N†</a> <a id="8432" href="plfa.More.html#18430" class="Function Operator">[</a> <a id="8434" href="plfa.Bisimulation.html#8350" class="Bound">M†</a> <a id="8437" href="plfa.More.html#18430" class="Function Operator">]</a><a id="8438" class="Symbol">)</a>
<a id="8440" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#8311" class="Function">~sub</a> <a id="8445" class="Symbol">{</a><a id="8446" href="plfa.Bisimulation.html#8446" class="Bound">Γ</a><a id="8447" class="Symbol">}</a> <a id="8449" class="Symbol">{</a><a id="8450" href="plfa.Bisimulation.html#8450" class="Bound">A</a><a id="8451" class="Symbol">}</a> <a id="8453" class="Symbol">{</a><a id="8454" href="plfa.Bisimulation.html#8454" class="Bound">B</a><a id="8455" class="Symbol">}</a> <a id="8457" href="plfa.Bisimulation.html#8457" class="Bound">~N</a> <a id="8460" href="plfa.Bisimulation.html#8460" class="Bound">~M</a> <a id="8463" class="Symbol">=</a> <a id="8465" href="plfa.Bisimulation.html#7462" class="Function">~subst</a> <a id="8472" class="Symbol">{</a><a id="8473" href="plfa.Bisimulation.html#8446" class="Bound">Γ</a> <a id="8475" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14672" class="InductiveConstructor Operator">,</a> <a id="8477" href="plfa.Bisimulation.html#8454" class="Bound">B</a><a id="8478" class="Symbol">}</a> <a id="8480" class="Symbol">{</a><a id="8481" href="plfa.Bisimulation.html#8446" class="Bound">Γ</a><a id="8482" class="Symbol">}</a> <a id="8484" href="plfa.Bisimulation.html#8504" class="Function">~σ</a> <a id="8487" class="Symbol">{</a><a id="8488" href="plfa.Bisimulation.html#8450" class="Bound">A</a><a id="8489" class="Symbol">}</a> <a id="8491" href="plfa.Bisimulation.html#8457" class="Bound">~N</a>
  <a id="8496" class="Keyword">where</a>
  <a id="8504" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#8504" class="Function">~σ</a> <a id="8507" class="Symbol">:</a> <a id="8509" class="Symbol">∀</a> <a id="8511" class="Symbol">{</a><a id="8512" href="plfa.Bisimulation.html#8512" class="Bound">A</a><a id="8513" class="Symbol">}</a> <a id="8515" class="Symbol">→</a> <a id="8517" class="Symbol">(</a><a id="8518" href="plfa.Bisimulation.html#8518" class="Bound">x</a> <a id="8520" class="Symbol">:</a> <a id="8522" href="plfa.Bisimulation.html#8446" class="Bound">Γ</a> <a id="8524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14672" class="InductiveConstructor Operator">,</a> <a id="8526" href="plfa.Bisimulation.html#8454" class="Bound">B</a> <a id="8528" href="plfa.More.html#14756" class="Datatype Operator">∋</a> <a id="8530" href="plfa.Bisimulation.html#8512" class="Bound">A</a><a id="8531" class="Symbol">)</a> <a id="8533" class="Symbol">→</a> <a id="8535" class="Symbol">_</a> <a id="8537" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="8539" class="Symbol">_</a>
  <a id="8543" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#8504" class="Function">~σ</a> <a id="8546" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14792" class="InductiveConstructor">Z</a>      <a id="8553" class="Symbol">=</a>  <a id="8556" href="plfa.Bisimulation.html#8460" class="Bound">~M</a>
  <a id="8561" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#8504" class="Function">~σ</a> <a id="8564" class="Symbol">(</a><a id="8565" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14839" class="InductiveConstructor Operator">S</a> <a id="8567" href="plfa.Bisimulation.html#8567" class="Bound">x</a><a id="8568" class="Symbol">)</a>  <a id="8571" class="Symbol">=</a>  <a id="8574" href="plfa.Bisimulation.html#3845" class="InductiveConstructor">~`</a>
</pre>{% endraw %}Once more, the structure of the proof resembles the original.


## The relation is a simulation

Finally, we can show that the relation actually is a simulation.
In fact, we will show the stronger condition of a lock-step simulation.
What we wish to show is:

_Lock-step simulation_: For every `M`, `M†`, and `N`:
If `M ~ M†` and `M —→ N`
then `M† —→ N†` and `N ~ N†`
for some `N†`.

Or, in a diagram:

    M  --- —→ --- N
    |             |
    |             |
    ~             ~
    |             |
    |             |
    M† --- —→ --- N†

We first formulate a concept corresponding to the lower leg
of the diagram, that is, its right and bottom edges:
{% raw %}<pre class="Agda"><a id="9243" class="Keyword">data</a> <a id="Leg"></a><a id="9248" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9248" class="Datatype">Leg</a> <a id="9252" class="Symbol">{</a><a id="9253" href="plfa.Bisimulation.html#9253" class="Bound">Γ</a> <a id="9255" href="plfa.Bisimulation.html#9255" class="Bound">A</a><a id="9256" class="Symbol">}</a> <a id="9258" class="Symbol">(</a><a id="9259" href="plfa.Bisimulation.html#9259" class="Bound">M†</a> <a id="9262" href="plfa.Bisimulation.html#9262" class="Bound">N</a> <a id="9264" class="Symbol">:</a> <a id="9266" href="plfa.Bisimulation.html#9253" class="Bound">Γ</a> <a id="9268" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14947" class="Datatype Operator">⊢</a> <a id="9270" href="plfa.Bisimulation.html#9255" class="Bound">A</a><a id="9271" class="Symbol">)</a> <a id="9273" class="Symbol">:</a> <a id="9275" class="PrimitiveType">Set</a> <a id="9279" class="Keyword">where</a>

  <a id="Leg.leg"></a><a id="9288" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9288" class="InductiveConstructor">leg</a> <a id="9292" class="Symbol">:</a> <a id="9294" class="Symbol">∀</a> <a id="9296" class="Symbol">{</a><a id="9297" href="plfa.Bisimulation.html#9297" class="Bound">N†</a> <a id="9300" class="Symbol">:</a> <a id="9302" href="plfa.Bisimulation.html#9253" class="Bound">Γ</a> <a id="9304" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14947" class="Datatype Operator">⊢</a> <a id="9306" href="plfa.Bisimulation.html#9255" class="Bound">A</a><a id="9307" class="Symbol">}</a>
    <a id="9313" class="Symbol">→</a> <a id="9315" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9262" class="Bound">N</a> <a id="9317" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="9319" href="plfa.Bisimulation.html#9297" class="Bound">N†</a>
    <a id="9326" class="Symbol">→</a> <a id="9328" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9259" class="Bound">M†</a> <a id="9331" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#19543" class="Datatype Operator">—→</a> <a id="9334" href="plfa.Bisimulation.html#9297" class="Bound">N†</a>
      <a id="9343" class="Comment">--------</a>
    <a id="9356" class="Symbol">→</a> <a id="9358" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9248" class="Datatype">Leg</a> <a id="9362" href="plfa.Bisimulation.html#9259" class="Bound">M†</a> <a id="9365" href="plfa.Bisimulation.html#9262" class="Bound">N</a>
</pre>{% endraw %}For our formalisation, in this case, we can use a stronger
relation than `—↠`, replacing it by `—→`.

We can now state and prove that the relation is a simulation.
Again, in this case, we can use a stronger relation than
`—↠`, replacing it by `—→`:
{% raw %}<pre class="Agda"><a id="sim"></a><a id="9624" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9624" class="Function">sim</a> <a id="9628" class="Symbol">:</a> <a id="9630" class="Symbol">∀</a> <a id="9632" class="Symbol">{</a><a id="9633" href="plfa.Bisimulation.html#9633" class="Bound">Γ</a> <a id="9635" href="plfa.Bisimulation.html#9635" class="Bound">A</a><a id="9636" class="Symbol">}</a> <a id="9638" class="Symbol">{</a><a id="9639" href="plfa.Bisimulation.html#9639" class="Bound">M</a> <a id="9641" href="plfa.Bisimulation.html#9641" class="Bound">M†</a> <a id="9644" href="plfa.Bisimulation.html#9644" class="Bound">N</a> <a id="9646" class="Symbol">:</a> <a id="9648" href="plfa.Bisimulation.html#9633" class="Bound">Γ</a> <a id="9650" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14947" class="Datatype Operator">⊢</a> <a id="9652" href="plfa.Bisimulation.html#9635" class="Bound">A</a><a id="9653" class="Symbol">}</a>
  <a id="9657" class="Symbol">→</a> <a id="9659" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9639" class="Bound">M</a> <a id="9661" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="9663" href="plfa.Bisimulation.html#9641" class="Bound">M†</a>
  <a id="9668" class="Symbol">→</a> <a id="9670" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9639" class="Bound">M</a> <a id="9672" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#19543" class="Datatype Operator">—→</a> <a id="9675" href="plfa.Bisimulation.html#9644" class="Bound">N</a>
    <a id="9681" class="Comment">---------</a>
  <a id="9693" class="Symbol">→</a> <a id="9695" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9248" class="Datatype">Leg</a>  <a id="9700" href="plfa.Bisimulation.html#9641" class="Bound">M†</a> <a id="9703" href="plfa.Bisimulation.html#9644" class="Bound">N</a>
<a id="9705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9624" class="Function">sim</a> <a id="9709" href="plfa.Bisimulation.html#3845" class="InductiveConstructor">~`</a>              <a id="9725" class="Symbol">()</a>
<a id="9728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9624" class="Function">sim</a> <a id="9732" class="Symbol">(</a><a id="9733" href="plfa.Bisimulation.html#3903" class="InductiveConstructor Operator">~ƛ</a> <a id="9736" href="plfa.Bisimulation.html#9736" class="Bound">~N</a><a id="9738" class="Symbol">)</a>         <a id="9748" class="Symbol">()</a>
<a id="9751" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9624" class="Function">sim</a> <a id="9755" class="Symbol">(</a><a id="9756" href="plfa.Bisimulation.html#9756" class="Bound">~L</a> <a id="9759" href="plfa.Bisimulation.html#3988" class="InductiveConstructor Operator">~·</a> <a id="9762" href="plfa.Bisimulation.html#9762" class="Bound">~M</a><a id="9764" class="Symbol">)</a>      <a id="9771" class="Symbol">(</a><a id="9772" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#19609" class="InductiveConstructor">ξ-·₁</a> <a id="9777" href="plfa.Bisimulation.html#9777" class="Bound">L—→</a><a id="9780" class="Symbol">)</a>
  <a id="9784" class="Keyword">with</a> <a id="9789" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9624" class="Function">sim</a> <a id="9793" href="plfa.Bisimulation.html#9756" class="Bound">~L</a> <a id="9796" href="plfa.Bisimulation.html#9777" class="Bound">L—→</a>
<a id="9800" class="Symbol">...</a>  <a id="9805" class="Symbol">|</a> <a id="9807" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9288" class="InductiveConstructor">leg</a> <a id="9811" href="plfa.Bisimulation.html#9811" class="Bound">~L′</a> <a id="9815" href="plfa.Bisimulation.html#9815" class="Bound">L†—→</a>                 <a id="9836" class="Symbol">=</a>  <a id="9839" href="plfa.Bisimulation.html#9288" class="InductiveConstructor">leg</a> <a id="9843" class="Symbol">(</a><a id="9844" href="plfa.Bisimulation.html#9811" class="Bound">~L′</a> <a id="9848" href="plfa.Bisimulation.html#3988" class="InductiveConstructor Operator">~·</a> <a id="9851" class="Bound">~M</a><a id="9853" class="Symbol">)</a>   <a id="9857" class="Symbol">(</a><a id="9858" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#19609" class="InductiveConstructor">ξ-·₁</a> <a id="9863" href="plfa.Bisimulation.html#9815" class="Bound">L†—→</a><a id="9867" class="Symbol">)</a>
<a id="9869" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9624" class="Function">sim</a> <a id="9873" class="Symbol">(</a><a id="9874" href="plfa.Bisimulation.html#9874" class="Bound">~V</a> <a id="9877" href="plfa.Bisimulation.html#3988" class="InductiveConstructor Operator">~·</a> <a id="9880" href="plfa.Bisimulation.html#9880" class="Bound">~M</a><a id="9882" class="Symbol">)</a>      <a id="9889" class="Symbol">(</a><a id="9890" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#19718" class="InductiveConstructor">ξ-·₂</a> <a id="9895" href="plfa.Bisimulation.html#9895" class="Bound">VV</a> <a id="9898" href="plfa.Bisimulation.html#9898" class="Bound">M—→</a><a id="9901" class="Symbol">)</a>
  <a id="9905" class="Keyword">with</a> <a id="9910" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9624" class="Function">sim</a> <a id="9914" href="plfa.Bisimulation.html#9880" class="Bound">~M</a> <a id="9917" href="plfa.Bisimulation.html#9898" class="Bound">M—→</a>
<a id="9921" class="Symbol">...</a>  <a id="9926" class="Symbol">|</a> <a id="9928" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9288" class="InductiveConstructor">leg</a> <a id="9932" href="plfa.Bisimulation.html#9932" class="Bound">~M′</a> <a id="9936" href="plfa.Bisimulation.html#9936" class="Bound">M†—→</a>                 <a id="9957" class="Symbol">=</a>  <a id="9960" href="plfa.Bisimulation.html#9288" class="InductiveConstructor">leg</a> <a id="9964" class="Symbol">(</a><a id="9965" class="Bound">~V</a> <a id="9968" href="plfa.Bisimulation.html#3988" class="InductiveConstructor Operator">~·</a> <a id="9971" href="plfa.Bisimulation.html#9932" class="Bound">~M′</a><a id="9974" class="Symbol">)</a>   <a id="9978" class="Symbol">(</a><a id="9979" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#19718" class="InductiveConstructor">ξ-·₂</a> <a id="9984" class="Symbol">(</a><a id="9985" href="plfa.Bisimulation.html#4945" class="Function">~val</a> <a id="9990" class="Bound">~V</a> <a id="9993" class="Bound">VV</a><a id="9995" class="Symbol">)</a> <a id="9997" href="plfa.Bisimulation.html#9936" class="Bound">M†—→</a><a id="10001" class="Symbol">)</a>
<a id="10003" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9624" class="Function">sim</a> <a id="10007" class="Symbol">((</a><a id="10009" href="plfa.Bisimulation.html#3903" class="InductiveConstructor Operator">~ƛ</a> <a id="10012" href="plfa.Bisimulation.html#10012" class="Bound">~N</a><a id="10014" class="Symbol">)</a> <a id="10016" href="plfa.Bisimulation.html#3988" class="InductiveConstructor Operator">~·</a> <a id="10019" href="plfa.Bisimulation.html#10019" class="Bound">~V</a><a id="10021" class="Symbol">)</a> <a id="10023" class="Symbol">(</a><a id="10024" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#19841" class="InductiveConstructor">β-ƛ</a> <a id="10028" href="plfa.Bisimulation.html#10028" class="Bound">VV</a><a id="10030" class="Symbol">)</a>        <a id="10039" class="Symbol">=</a>  <a id="10042" href="plfa.Bisimulation.html#9288" class="InductiveConstructor">leg</a> <a id="10046" class="Symbol">(</a><a id="10047" href="plfa.Bisimulation.html#8311" class="Function">~sub</a> <a id="10052" href="plfa.Bisimulation.html#10012" class="Bound">~N</a> <a id="10055" href="plfa.Bisimulation.html#10019" class="Bound">~V</a><a id="10057" class="Symbol">)</a>  <a id="10060" class="Symbol">(</a><a id="10061" href="plfa.More.html#19841" class="InductiveConstructor">β-ƛ</a> <a id="10065" class="Symbol">(</a><a id="10066" href="plfa.Bisimulation.html#4945" class="Function">~val</a> <a id="10071" href="plfa.Bisimulation.html#10019" class="Bound">~V</a> <a id="10074" href="plfa.Bisimulation.html#10028" class="Bound">VV</a><a id="10076" class="Symbol">))</a>
<a id="10079" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9624" class="Function">sim</a> <a id="10083" class="Symbol">(</a><a id="10084" href="plfa.Bisimulation.html#4112" class="InductiveConstructor">~let</a> <a id="10089" href="plfa.Bisimulation.html#10089" class="Bound">~M</a> <a id="10092" href="plfa.Bisimulation.html#10092" class="Bound">~N</a><a id="10094" class="Symbol">)</a>    <a id="10099" class="Symbol">(</a><a id="10100" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#20891" class="InductiveConstructor">ξ-let</a> <a id="10106" href="plfa.Bisimulation.html#10106" class="Bound">M—→</a><a id="10109" class="Symbol">)</a>
  <a id="10113" class="Keyword">with</a> <a id="10118" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9624" class="Function">sim</a> <a id="10122" href="plfa.Bisimulation.html#10089" class="Bound">~M</a> <a id="10125" href="plfa.Bisimulation.html#10106" class="Bound">M—→</a>
<a id="10129" class="Symbol">...</a>  <a id="10134" class="Symbol">|</a> <a id="10136" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9288" class="InductiveConstructor">leg</a> <a id="10140" href="plfa.Bisimulation.html#10140" class="Bound">~M′</a> <a id="10144" href="plfa.Bisimulation.html#10144" class="Bound">M†—→</a>                 <a id="10165" class="Symbol">=</a>  <a id="10168" href="plfa.Bisimulation.html#9288" class="InductiveConstructor">leg</a> <a id="10172" class="Symbol">(</a><a id="10173" href="plfa.Bisimulation.html#4112" class="InductiveConstructor">~let</a> <a id="10178" href="plfa.Bisimulation.html#10140" class="Bound">~M′</a> <a id="10182" class="Bound">~N</a><a id="10184" class="Symbol">)</a> <a id="10186" class="Symbol">(</a><a id="10187" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#19718" class="InductiveConstructor">ξ-·₂</a> <a id="10192" href="plfa.More.html#18941" class="InductiveConstructor">V-ƛ</a> <a id="10196" href="plfa.Bisimulation.html#10144" class="Bound">M†—→</a><a id="10200" class="Symbol">)</a>
<a id="10202" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9624" class="Function">sim</a> <a id="10206" class="Symbol">(</a><a id="10207" href="plfa.Bisimulation.html#4112" class="InductiveConstructor">~let</a> <a id="10212" href="plfa.Bisimulation.html#10212" class="Bound">~V</a> <a id="10215" href="plfa.Bisimulation.html#10215" class="Bound">~N</a><a id="10217" class="Symbol">)</a>    <a id="10222" class="Symbol">(</a><a id="10223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#21013" class="InductiveConstructor">β-let</a> <a id="10229" href="plfa.Bisimulation.html#10229" class="Bound">VV</a><a id="10231" class="Symbol">)</a>      <a id="10238" class="Symbol">=</a>  <a id="10241" href="plfa.Bisimulation.html#9288" class="InductiveConstructor">leg</a> <a id="10245" class="Symbol">(</a><a id="10246" href="plfa.Bisimulation.html#8311" class="Function">~sub</a> <a id="10251" href="plfa.Bisimulation.html#10215" class="Bound">~N</a> <a id="10254" href="plfa.Bisimulation.html#10212" class="Bound">~V</a><a id="10256" class="Symbol">)</a>  <a id="10259" class="Symbol">(</a><a id="10260" href="plfa.More.html#19841" class="InductiveConstructor">β-ƛ</a> <a id="10264" class="Symbol">(</a><a id="10265" href="plfa.Bisimulation.html#4945" class="Function">~val</a> <a id="10270" href="plfa.Bisimulation.html#10212" class="Bound">~V</a> <a id="10273" href="plfa.Bisimulation.html#10229" class="Bound">VV</a><a id="10275" class="Symbol">))</a>
</pre>{% endraw %}The proof is by case analysis, examining each possible instance of `M ~ M†`
and each possible instance of `M —→ M†`, using recursive invocation whenever
the reduction is by a `ξ` rule, and hence contains another reduction.
In its structure, it looks a little bit like a proof of progress:

* If the related terms are variables, no reduction applies.
* If the related terms are abstractions, no reduction applies.
* If the related terms are applications, there are three subcases:
  - The source term reduces via `ξ-·₁`, in which case the target term does as well.
    Recursive invocation gives us

        L  --- —→ ---  L′
        |              |
        |              |
        ~              ~
        |              |
        |              |
        L† --- —→ --- L′†

    from which follows:

         L · M  --- —→ ---  L′ · M
           |                   |
           |                   |
           ~                   ~
           |                   |
           |                   |
        L† · M† --- —→ --- L′† · M†

  - The source term reduces via `ξ-·₂`, in which case the target term does as well.
    Recursive invocation gives us

        M  --- —→ ---  M′
        |              |
        |              |
        ~              ~
        |              |
        |              |
        M† --- —→ --- M′†

    from which follows:

         V · M  --- —→ ---  V · M′
           |                  |
           |                  |
           ~                  ~
           |                  |
           |                  |
        V† · M† --- —→ --- V† · M′†

    Since simulation commutes with values and `V` is a value, `V†` is also a value.

  - The source term reduces via `β-ƛ`, in which case the target term does as well:

         (ƛ x ⇒ N) · V  --- —→ ---  N [ x := V ]
              |                           |
              |                           |
              ~                           ~
              |                           |
              |                           |
        (ƛ x ⇒ N†) · V† --- —→ --- N† [ x :=  V† ]

    Since simulation commutes with values and `V` is a value, `V†` is also a value.
    Since simulation commutes with substitution and `N ~ N†` and `V ~ V†`,
    we have `N [ x := V] ~ N† [ x := V† ]`.

* If the related terms are a let and an application of an abstraction,
  there are two subcases:

  - The source term reduces via `ξ-let`, in which case the target term
    reduces via `ξ-·₂`.  Recursive invocation gives us

        M  --- —→ ---  M′
        |              |
        |              |
        ~              ~
        |              |
        |              |
        M† --- —→ --- M′†

    from which follows:

        let x = M in N --- —→ --- let x = M′ in N
              |                         |
              |                         |
              ~                         ~
              |                         |
              |                         |
        (ƛ x ⇒ N) · M  --- —→ --- (ƛ x ⇒ N) · M′

  - The source term reduces via `β-let`, in which case the target
    term reduces via `β-ƛ`:

        let x = V in N  --- —→ ---  N [ x := V ]
              |                         |
              |                         |
              ~                         ~
              |                         |
              |                         |
        (ƛ x ⇒ N†) · V† --- —→ --- N† [ x := V ]

    Since simulation commutes with values and `V` is a value, `V†` is also a value.
    Since simulation commutes with substitution and `N ~ N†` and `V ~ V†`,
    we have `N [ x := V] ~ N† [ x := V† ]`.


#### Exercise `sim⁻¹`

Show that we also have a simulation in the other direction, and hence that we have
a bisimulation.

{% raw %}<pre class="Agda"><a id="14043" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `products`

Show that the two formulations of products in
Chapter [More]({{ site.baseurl }}/More/)
are in bisimulation.  The only constructs you need to include are
variables, and those connected to functions and products.
In this case, the simulation is _not_ lock-step.

{% raw %}<pre class="Agda"><a id="14362" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Unicode

This chapter uses the following unicode:

    †  U+2020  DAGGER (\dag)
    ⁻  U+207B  SUPERSCRIPT MINUS (\^-)
    ¹  U+00B9  SUPERSCRIPT ONE (\^1)
