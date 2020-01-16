Proof of Lemma [\[lem:delta\]](#lem:delta){reference-type="ref" reference="lem:delta"}
======================================================================================

Consider the estimate $\hat{O}_w(t)$ that the algorithm uses at node $v$
for neighbor $w$ at time $t$. By definition of $\Tmax$, the measurement
is based on clock values $L_v(t_v)$ and $L_w(t_w)$ for some
$t_v,t_w\in [t-\Tmax,t)$. Without loss of generality, we assume that to
measure whether $L_w-L_v\ge T\in \R$, the signals are sent at logical
times satisfying $L_w(t_w)-T=L_v(t_v)$.[^1] Denote by $t_v'\in (t_v,t)$
and $t_w'\in (t_w,t)$ the times when the respective signals arrive at
the data or clock input, respectively, of the register[^2] indicating
whether $\hat{O}_w\ge T$ for a given threshold $T$. By definition of
$\delta_0$, we have that $$\abs{t_v'-t_v-(t_w'-t_w)}\le \delta_0.$$ Note
that the register indicates $\hat{O}_w(t)\ge T$, i.e., latches $1$, if
and only if $t_w'<t_v'$.[^3] Thus, we need to show $$\begin{aligned}
L_w(t)-L_v(t)&\ge T+\delta \implies t_w'<t_v'\\
L_w(t)-L_v(t)&\le T-\delta \implies t_w'>t_v'.\end{aligned}$$ Assume
first that $L_w(t)-L_v(t)\ge T+\delta$. Then, using **I4** and that
$L_w(t_w)-T=L_v(t_v)$, we can bound $$\begin{aligned}
T+\delta &\le L_w(t)-L_v(t)\\
&\le L_w(t_v)-L_v(t_v)+((1+\mu)(1+\rho)-1)(t-t_v)\\
&= L_w(t_v)-L_w(t_w)+T+(\mu+\rho+\rho \mu)(t-t_v)\\
&\le t_v-t_w+T+(\mu+\rho+\rho\mu)(t-\min\{t_v,t_w\})\\
&<t_v-t_w+T+(\mu+\rho+\rho\mu)\Tmax.\end{aligned}$$ Hence,
$$t_w'-t_v'\ge t_w-t_v-\delta_0 > \delta-\delta_0-(\mu+\rho+\rho\mu)\Tmax =0.$$
For the second implication, observe that it is equivalent to
$$L_v(t)-L_w(t)\ge -T+\delta \implies t_v'>t_w'.$$ As we have shown the
first implication for any $T\in \R$, the second follows analogously by
exchanging the roles of $v$ and $w$.

Proof of Theorem [\[thm:gcs\]](#thm:gcs){reference-type="ref" reference="thm:gcs"}
==================================================================================

In this appendix, we prove
Theorem [\[thm:gcs\]](#thm:gcs){reference-type="ref"
reference="thm:gcs"}. We assume that at (Newtonian) time $t = 0$, the
system satisfies *some* bound on local skew. The analysis we provide
shows that the GCS algorithm maintains a (slightly larger) bound on
local skew for all $t \geq 0$. An upper bound on the local skew also
bounds the number of values of $s$ for which **FC** or **SC**
(Definition [\[dfn:fast-slow-cond\]](#dfn:fast-slow-cond){reference-type="ref"
reference="dfn:fast-slow-cond"}) can hold, as a large $s$ implies a
large local skew. (For example, if a node $v$ satisfies **FC1** for some
$s$, then $v$ has a neighbor $x$ satisfying
$L_x(t) - L_v(t) \geq (2 s + 1) \kappa$, implying that
$\calL(t) \geq (2 s + 1) \kappa$.) Accordingly, an implementation need
only test for values of $s$ satisfying
$\abs{s} < \frac 1 {2 \kappa} \calL_{\mathrm{max}}$, where
$\calL_{\mathrm{max}}$ is a theoretical upper bound on the local skew.
Our analysis also shows that given an arbitrary initial global skew
$\calG(0)$, the system will converge to the skew bounds claimed in
Theorem [\[thm:gcs\]](#thm:gcs){reference-type="ref"
reference="thm:gcs"} within time $O(\calG(0)/\mu)$. We note that the
skew upper bounds of
Theorem [\[thm:gcs\]](#thm:gcs){reference-type="ref"
reference="thm:gcs"} match the theoretical lower bounds
of [@lenzen10tight] up to a factor of approximately 2, and the
theoretical lower bounds can be acheived even by systems with initially
perfect synchronization (i.e., systems with $\calL(0) = \calG(0) = 0$).

Our analysis also assumes that logical clocks are differentiable
functions. This assumption is without loss of generality: By the
Stone-Weierstrass Theorem (cf. Theorem 7.26 in [@Rudin1976-principles])
every continuous function on a compact interval can be approximated
arbitrarily closely by a differentiable function.

We will rely on the following technical result. We provide a proof in
Section [2.5](#sec:max-bound){reference-type="ref"
reference="sec:max-bound"}.

[\[lem:max-bound\]]{#lem:max-bound label="lem:max-bound"} For
$k \in \Zpos$ and $t_0, t_1 \in \nnR$ with $t_0 < t_1$, let
$\mathcal{F} = \{f_i\,|\,i\in [k]\}$, where each
$f_i \colon [t_0, t_1] \to \R$ is a differentiable function. Define
$F \colon [t_0, t_1] \to \R$ by $F(t) =  \max_{i\in [k]} \set{f_i(t)}$.
Suppose $\mathcal{F}$ has the property that for every $i$ and $t$, if
$f_i(t) = F(t)$, then $\frac{d}{dt} f_i(t) \leq r$. Then for all
$t \in [t_0, t_1]$, we have $F(t) \leq F(t_0) + r (t - t_0)$.

Throughout this section, we assume that each node runs an algorithm
satisfying the invariants stated in
[\[dfn:gcs-implementation\]](#dfn:gcs-implementation){reference-type="ref"
reference="dfn:gcs-implementation"}. By
[\[lem:uncertainty\]](#lem:uncertainty){reference-type="ref"
reference="lem:uncertainty"},
[\[alg:ogcs\]](#alg:ogcs){reference-type="ref" reference="alg:ogcs"}
meets this requirement if $\kappa > 2\delta+2(\rho+\mu+\rho\mu)\Tmax$.

Leading Nodes
-------------

We start by showing that skew cannot build up too quickly. This is
captured by analyzing the following functions.

[\[def:psi\]]{#def:psi label="def:psi"} For each $v\in V$, $s \in \N$,
and $t \in \nnR$, we define
$$\Psi_v^s(t) = \max_{w\in V} \{L_w(t) - L_v(t) -  2 s \kappa d(v,w)\},$$
where $d(v,w)$ denotes the distance between $v$ and $w$ in $G$.
Moreover, set $$\Psi^s(t) = \max_{v\in V} \{\Psi_v^s(t)\}.$$ Finally, we
say that $w\in V$ is a *leading node* if there is some $v\in V$
satisfying $$\Psi_v^s(t) = L_w(t) - L_v(t) - 2 s \kappa d(v,w) > 0.$$

Observe that any bound on $\Psi^s$ implies a corresponding bound on
$\calL$: If $\Psi^s(t) \leq \kappa$, then for any adjacent nodes $v, w$
we have $L_w(t) - L_v(t) - 2 s \kappa \leq \Psi^s(t) \leq \kappa$.
Therefore, $\Psi^s(t) \leq \kappa \implies \calL \leq (2 s + 1) \kappa$.
Our analysis will show that in general,
$\Psi^s(t) \leq \Gmax / \sigma^s$ for every $s \in \N$ and all times
$t$. In particular, considering
$s=\lceil\log_{\mu / \rho} \Gmax/\kappa\rceil$ gives a bound on $\calL$
in terms of $\Gmax$. Because $\calG(t)=\Psi^0(t)$, the skew bounds will
then follow if we can suitably bound $\Psi^0$ at all times.

Note that the definition of $\Psi_v^s$ is closely related to the
definition of the slow condition. In fact, the following lemma shows
that if $w$ is a leading node, then $w$ satisfies the slow condition.
Thus, $\Psi^s$ cannot increase quickly: **I4**
(Def. [\[dfn:gcs-implementation\]](#dfn:gcs-implementation){reference-type="ref"
reference="dfn:gcs-implementation"}) then stipulates that leading nodes
increase their logical clocks at rate at most $1+\rho$. This behavior
allows nodes in fast mode to catch up to leading nodes.

[\[lemma:leading\]]{#lemma:leading label="lemma:leading"} Suppose
$w \in V$ is a leading node at time $t$. Then
$\der{t}L_w(t)=\der{t}H_w(t)\in [1,1+\rho]$.

By **I4**, the claim follows if $w$ satisfies the slow condition at time
$t$. As $w$ is a leading node at time $t$, there are $s \in \N$ and
$v \in V$ satisfying
$$\Psi_v^s(t) = L_w(t) - L_v(t) - 2s \kappa d(v,w) > 0.$$ In particular,
$L_w(t)>L_v(t)$, so $w\neq v$. For any $y\in V$, we have
$$\begin{aligned}
  L_w(t) - L_v(t) - 2 s \kappa d(v,w) &= \Psi_v^s(t)\\
  &\geq L_y(t) - L_v(t) - 2 s \kappa d(y,w).\end{aligned}$$ Rearranging
this expression yields
$$L_w(t) - L_y(t) \geq 2 s \kappa (d(v,w)-d(y,w)).$$ In particular, for
any $y \in N_v$, $d(v,w) \geq d(y,w) - 1$ and hence
$$L_y(t) - L_w(t) \leq 2s \kappa,$$ i.e., SC2 holds for $s$ at $w$.

Now consider $x \in N_v$ so that $d(x,w) = d(v,w) - 1$. Such a node
exists because $v \neq w$. We obtain
$$L_w(t) - L_y(t) \geq 2 s \kappa.$$ Thus SC1 is satisfied for $s$,
i.e., indeed the slow condition holds at $w$ at time $t$.

Lemma [\[lemma:leading\]](#lemma:leading){reference-type="ref"
reference="lemma:leading"} can readily be translated into a bound on the
growth of $\Psi_w^s$ whenever $\Psi_w^s > 0$.

[\[lemma:wait\_up\]]{#lemma:wait_up label="lemma:wait_up"} Suppose
$w \in V$ satisfies $\Psi_w^s(t) > 0$ for all $t \in (t_0, t_1]$. Then
$$\Psi_w^s(t_1) \leq \Psi_w^s(t_0) - (L_w(t_1) - L_w(t_0)) + (1 + \rho) (t_1 - t_0).$$

Fix $w \in V$, $s \in \N$ and $(t_0, t_1]$ as in the hypothesis of the
lemma. For $v \in V$ and $t \in (t_0, t_1]$, define the function
$f_v(t) = L_v(t) - 2 s \kappa d(v,w)$. Observe that
$$\max_{v \in V} \{f_v(t)\}-L_w(t) = \Psi_w^s(t)\,.$$ Moreover, for any
$v$ satisfying $f_v(t) = L_w(t) + \Psi_w^s(t)$, we have
$L_v(t) - L_w(t) - 2s \kappa d(v,w) = \Psi_w^s(t) > 0$. Thus,
Lemma [\[lemma:leading\]](#lemma:leading){reference-type="ref"
reference="lemma:leading"} shows that $v$ is in slow mode at time $t$.
As (we assume that) logical clocks are differentiable, so is $f_v$, and
it follows that $\der{t}f_v(t) \leq 1 + \rho$ for any $v \in V$ and time
$t \in (t_0,t_1]$ satisfying $f_v(t) = \max_{x\in V} \{f_x(t)\}$. By
Lemma [\[lem:max-bound\]](#lem:max-bound){reference-type="ref"
reference="lem:max-bound"}, it follows that $\max_{v\in V}\{f_v(t)\}$
grows at most at rate $1 + \rho$:
$$\max_{v \in V} \{f_v(t_1)\}\leq \max_{v \in V} \{f_v(t_0)\}+(1+\rho)(t_1-t_0)\,.$$

We conclude that $$\begin{aligned}
  \Psi_w^s(t_1) - \Psi_w^s(t_0) &= \max_{v \in V} \{f_v(t_1)\} - L_w(t_1)\\
  &\qquad - (\max_{v \in V} \{f_v(t_0)\} - L_w(t_0))\\
  &\leq (1+\rho)(t_1 - t_0)-(L_w(t_1) - L_w(t_0)),\end{aligned}$$ which
can be rearranged into the desired result.

[\[cor:wait\_up\]]{#cor:wait_up label="cor:wait_up"} For all $s\in \N$
and times $t_1\geq t_0$, $\Psi^s(t_1)\le \Psi^s(t_0) + \rho (t_1-t_0)$.

Choose $w\in V$ such that $\Psi^s(t_1)=\Psi_w^s(t_1)$. As
$\Psi_w^s(t)\geq 0$ for all times $t$, nothing is to show if
$\Psi^s(t_1)=0$. Let $t\in [t_0,t_1)$ be the supremum of times from
$t'\in [t_0,t_1)$ with the property that $\Psi_w^s(t')=0$. Because
$\Psi_w^s$ is continuous, $t\neq t_0$ implies that $\Psi_w^s(t)=0$.
Hence, $\Psi_w^s(t)\le \Psi_w^s(t_0)$. By **I2** and
[\[lemma:wait\_up\]](#lemma:wait_up){reference-type="ref"
reference="lemma:wait_up"}, we get that $$\begin{aligned}
\Psi^s(t_1)&=\Psi_w^s(t_1)\\
&\le \Psi_w^s(t) - (L_w(t_1) - L_w(t)) + (1 + \rho) (t_1 - t)\\
&\le \Psi_w^s(t)+\rho(t_1-t)\\
&\le \Psi_w^s(t_0)+\rho(t_1-t_0)\\
&\le \Psi^s(t_0)+\rho(t_1-t_0).\qedhere\end{aligned}$$

Trailing Nodes {#trailing-nodes .unnumbered}
--------------

As $L_w(t_1) - L_w(t_0) \geq t_1-t_0$ at all times by **I2**,
Lemma [\[lemma:catch\_up\]](#lemma:catch_up){reference-type="ref"
reference="lemma:catch_up"} implies that $\Psi^s$ cannot grow faster
than at rate $\rho$ when $\Psi^s(t) > 0$. This means that nodes whose
clocks are far behind leading nodes can catch up, so long as the lagging
nodes satisfy the fast condition and thus run at rate at least $1+\mu$
by **I3**. Our next task is to show that "trailing nodes" always satisfy
the fast condition so that they are never too far behind leading nodes.
The approach to showing this is similar to the one for
Lemma [\[lemma:wait\_up\]](#lemma:wait_up){reference-type="ref"
reference="lemma:wait_up"}, where now we need to exploit the fast
condition.

For each $v\in V$, $s \in \N$, and $t \in \nnR$, we define
$$\Xi_v^s(t) = \max_{w\in V} \{L_v(t) - L_w(t) -  (2 s + 1) \kappa d(v,w)\},$$
where $d(v,w)$ denotes the distance between $v$ and $w$ in $G$.
Moreover, set $$\Xi^s(t) = \max_{v\in V} \{\Xi_v^s(t)\}.$$ Finally, we
say that $w\in V$ is a *trailing node* at time $t$, if there is some
$v\in V$ satisfying
$$\Xi_v^s(t) = L_v(t) - L_w(t) - (2 s + 1) \kappa d(v,w) > 0.$$

[\[lemma:trailing\]]{#lemma:trailing label="lemma:trailing"} If
$w \in V$ is a trailing node at time $t$, then
$\der{t}L_w(t)=(1+\mu)\der{t}H_w(t)\in [1+\mu,(1+\rho)(1+\mu)]$.

By **I3**, it suffices to show that $w$ satisfies the fast condition at
time $t$. Let $s$ and $v$ satisfy $$\begin{aligned}
    &L_v(t)-L_w(t) - (2s + 1) \kappa d(v,w)\\
    &\qquad = \max_{x\in V} \{L_v(t) - L_x(t) - (2 s + 1) \kappa d(v,x)\} > 0.
  \end{aligned}$$ In particular, $L_v(t)>L_w(t)$, implying that
$v \neq w$. For $y \in V$, we have $$\begin{aligned}
    &L_v(t) - L_w(t) - (2s + 1) \kappa d(v,w)\\
    &\qquad \geq L_v(t) - L_y(t) - (2s + 1) \kappa d(v,y).
  \end{aligned}$$ Thus for all neighbors $y\in N_w$,
$$L_y(t) - L_w(t) + (2s + 1) \kappa (d(v,y) - d(v,w)) \geq 0.$$ It
follows that
$$\forall y \in N_v \colon L_w(t) - L_y(t) \leq (2s + 1)\kappa,$$ i.e.,
FC2 holds for $s$. As $v\neq w$, there is some node $x \in N_v$ with
$d(v,x) = d(v,w) - 1$. Thus we obtain
$$\exists x \in N_v\colon L_y(t) - L_w(t) \geq (2s + 1)\kappa,$$ showing
FC1 for $s$, i.e., indeed the fast condition holds at $w$ at time $t$.

Using Lemma [\[lemma:trailing\]](#lemma:trailing){reference-type="ref"
reference="lemma:trailing"}, we can show that if $\Psi^s_w(t_0)>0$, $w$
will eventually catch up. How long this takes can be expressed in terms
of $\Psi^{s-1}(t_0)$, or, if $s=0$, $\calG$.

[\[lemma:catch\_up\]]{#lemma:catch_up label="lemma:catch_up"} Let
$s\in \N$ and $v,w\in V$. Let $t_0$ and $t_1$ be times satisfying that
$$t_1 \geq t_0 + \frac{\Xi_v^s(t_0)}{\mu}.$$ Then
$$L_w(t_1) \geq t_1 - t_0 + L_v(t_0)-(2s+1)\kappa d(v,w).$$

W.l.o.g., we may assume that $t_1=t_0 + \Xi_v^s(t_0)/\mu$, as **I2**
ensures that $\der{t}L_w(t)\geq 1$ at all times, i.e., the general
statement readily follows. For any $x \in V$, define
$$f_x(t) = t - t_0 + L_v(t_0) - L_x(t) - (2s + 1) \kappa d(v,x).$$ Again
by **I2**, it thus suffices to show that $f_w(t)\le 0$ for some
$t\in [t_0, t_1]$.

Observe that $\Xi_v^s(t_0)=\max_{x\in V} \{f_x(t_0)\}$. Thus, it
suffices to show that $\max_{x\in V} \{f_x(t)\}$ decreases at rate $\mu$
so long as it is positive, as then
$f_w(t_1)\le \max_{x\in V} \{f_x(t_1)\} \le 0$. To this end, consider
any time $t\in [t_0,t_1]$ satisfying $\max_{x \in V} \{f_x(t)\} > 0$ and
let $y \in V$ be any node such that $\max_{x\in V} \{f_x(t)\} = f_y(t)$.
Then $y$ is trailing, as $$\begin{aligned}
    \Xi_v^s(t)&=\max_{x\in V}\{L_v(t)-L_x(t)-(2s+1)\kappa d(v,x)\}\\
    &= L_v(t)-L_v(t_0)-(t-t_0)+\max_{x\in V}\{f_x(t)\}\\
    &= L_v(t)-L_v(t_0)-(t-t_0)+f_y(t)\\
    &= L_v(t)-L_y(t)-(2s+1)\kappa d(v,y)
  \end{aligned}$$ and $$\begin{aligned}
    \Xi_v^s(t)&=L_v(t) - L_v(t_0) - (t - t_0) + \max_{x\in V} \{f_x(t)\}\\
    &> L_v(t) - L_v(t_0) - (t-t_0) \geq 0.
  \end{aligned}$$ Thus, by
Lemma [\[lemma:trailing\]](#lemma:trailing){reference-type="ref"
reference="lemma:trailing"} we have that $\der{t}L_y(t)\geq 1+\mu$,
implying $\der{t}f_y(t) = 1 - \der{t} L_y(t) \leq -\mu$.

To complete the proof, assume towards a contradiction that
$\max_{x\in V} \{f_x(t)\} > 0$ for all $t \in [t_0,t_1]$. Then, applying
Lemma [\[lem:max-bound\]](#lem:max-bound){reference-type="ref"
reference="lem:max-bound"} again, we conclude that $$\begin{aligned}
    \Xi_v^s(t_0)&=\max_{x\in V} \{f_x(t_0)\}\\
    &> -(\max_{x\in V} \{f_x(t_1)\} - \max_{x\in V} \{f_x(t_0)\})\\
    &\geq \mu(t_1-t_0) = \Xi_v^s(t_0),
  \end{aligned}$$ i.e., it must hold that
$f_w(t)\le \max_{x\in V} \{f_x(t)\}\le 0$ for some $t \in [t_0,t_1]$.

Base Case and Global Skew
-------------------------

We now prove that if $\Psi^s(0)$ is bounded for some $s\in \N$, it
cannot grow significantly and thus remains bounded. This will both serve
as an induction anchor for establishing our bound on the local skew and
for bounding the global skew, as $\Psi^0(t)=\calG(t)$. In addition, we
will deduce that even if the initial global skew $\calG(0)$ is large, at
times $t\geq \calG(0)/\mu$, $\calG(t)$ is bounded by
$\Gmax = (1-2\rho/\mu)\kappa D$.

To this end, we will apply
[\[lemma:catch\_up\]](#lemma:catch_up){reference-type="ref"
reference="lemma:catch_up"} in the following form.

[\[cor:catch\_up\_same\]]{#cor:catch_up_same label="cor:catch_up_same"}
Let $s\in \N$ and $t_0$, $t_1$ be times satisfying
$$t_1 \geq t_0 + \frac{\Psi^s(t_0)}{\mu}.$$ Then, for any $w \in V$ we
have $$L_w(t_1) - L_w(t_0) \geq t_1 - t_0 +
      \Psi_w^s(t_0) - \kappa \cdot D.$$

If $\Psi_w^s(t_0) - \kappa \cdot D\leq 0$, the claim is trivially
satisfied due to **I2** guaranteeing that $\der{t}L_w(t)\ge 1$ at all
times $t$. Hence, assume that $\Psi_w^s(t_0) - \kappa \cdot D>0$ and
choose any $v$ so that
$$\Psi_w^s(t_0) = L_v(t) - L_w(t) - 2s\kappa d(v,w).$$ We have that
$$\begin{aligned}
\Xi_v^s(t_0)&\ge L_v(t) - L_w(t) - (2s+1)\kappa d(v,w)\\
&\ge L_v(t) - L_w(t) - 2s\kappa d(v,w)-\kappa\cdot D\\
&=\Psi_w^s(t_0) - \kappa \cdot D.\end{aligned}$$ As trivially
$\Psi^s(t_0)\ge \Xi^s(t_0)\ge \Xi_v^s(t_0)$, we have that
$t_1\ge t_0 + \Xi_v^s(t_0)/\mu$ and the claim follows by applying
[\[lemma:catch\_up\]](#lemma:catch_up){reference-type="ref"
reference="lemma:catch_up"}.

Combining this corollary with
[\[lemma:wait\_up\]](#lemma:wait_up){reference-type="ref"
reference="lemma:wait_up"}, we can bound $\Psi^s$ at all times.

[\[lemma:psi\_bound\_same\]]{#lemma:psi_bound_same
label="lemma:psi_bound_same"} Fix $s\in \N$. If
$\Psi^s(0)\le \kappa \cdot D / (1-\rho^2/\mu^2)$, then
$$\Psi^s(t)\le \frac{\mu}{\mu-\rho}\cdot \kappa \cdot D.$$ at all times
$t$. Otherwise, $$\Psi^s(t)\le \begin{cases}
\left(1+\frac{\rho}{\mu}\right)\cdot\Psi^s(0) & \mbox{if }t\le \frac{\Psi^s(0)}{\mu}\\
\kappa \cdot D + \frac{\rho}{\mu}\cdot  \left(1+\frac{\rho}{\mu}\right)\cdot\Psi^s(0)
 & \mbox{else.}
\end{cases}$$

For $t\le \Psi^s(0)/\mu$, the claim follows immediately from
[\[cor:wait\_up\]](#cor:wait_up){reference-type="ref"
reference="cor:wait_up"} (and possibly using that
$\Psi^s(0)\le \kappa \cdot D / (1-\rho^2/\mu^2)$). Concerning larger
times, denote by $B$ the bound that needs to be shown and suppose that
$\Psi^s(t_1)=B+\varepsilon$ for some $\varepsilon>0$ and minimal
$t_1>\Psi^s(0)/\mu$. Choose $w\in V$ so that $\Psi_w^s(t_1)=\Psi^s(t_1)$
and $t_0$ such that $t_1 = t_0 + \Psi^s(t_0)/\mu$. Such a time must
exist, because the function $f(t)=t_1-t-\Psi^s(t)/\mu$ is continuous and
satisfies $$\begin{aligned}
f(t_1)=-\frac{\Psi^s(t_1)}{\mu}<0<t_1-\frac{\Psi^s(0)}{\mu}=f(t_0).\end{aligned}$$
We apply
[\[lemma:wait\_up,cor:catch\_up\_same\]](#lemma:wait_up,cor:catch_up_same){reference-type="ref"
reference="lemma:wait_up,cor:catch_up_same"}, showing that
$$\begin{aligned}
\Psi_w^s(t_1) &\le \Psi_w^s(t_0) - (L_w(t_1) - L_w(t_0)) + (1 + \rho) (t_1 - t_0)\\
&\le \kappa \cdot D + \rho (t_1-t_0)\\
&= \kappa\cdot D + \frac{\rho}{\mu}\Psi^s(t_0).\end{aligned}$$ We
distinguish two cases. If
$\Psi^s(0)\le \kappa \cdot D / (1-\rho^2/\mu^2)$, we have that
$$\Psi^s(t_0) < \frac{\mu}{\mu-\rho}\cdot \kappa \cdot D +\varepsilon,$$
because $t_0<t_1$, leading to the contradiction
$$\frac{\mu}{\mu-\rho}\cdot \kappa \cdot D + \varepsilon = \Psi^s(t_1)
< \left(1+\frac{\rho}{\mu-\rho}\right)\cdot \kappa \cdot D + \varepsilon.$$
On the other hand, if $\Psi^s(0)> \kappa \cdot D / (1-\rho^2/\mu^2)$,
this is equivalent to
$$\kappa \cdot D + \frac{\rho}{\mu}\cdot  \left(1+\frac{\rho}{\mu}\right)\cdot\Psi^s(0)
>\left(1+\frac{\rho}{\mu}\right)\cdot\Psi^s(0).$$ Hence,
$$\Psi^s(t_0) < \kappa \cdot D + \frac{\rho}{\mu}\cdot  \left(1+\frac{\rho}{\mu}\right)\cdot\Psi^s(0)+\varepsilon$$
and we get that $$\begin{aligned}
&\kappa \cdot D + \frac{\rho}{\mu}\cdot  \left(1+\frac{\rho}{\mu}\right)\cdot\Psi^s(0)+\varepsilon\\
 &\qquad= \Psi^s(t_1)\\
&\qquad< \kappa \cdot D + \frac{\rho}{\mu}\cdot \left(\kappa \cdot D + \frac{\rho}{\mu}\cdot  \left(1+\frac{\rho}{\mu}\right)\cdot\Psi^s(0) + \varepsilon\right).\end{aligned}$$
This implies the contradiction
$$\Psi^s(0)<\frac{\kappa \cdot D}{1+\rho/\mu}+\frac{\rho}{\mu}\cdot \Psi^s(0)$$
to $\Psi^s(0)>\kappa \cdot D/(1-\rho^2/\mu^2)$.

[\[cor:convergence\]]{#cor:convergence label="cor:convergence"}
Abbreviate $q=\frac{\rho}{\mu}\cdot \left(1+\frac{\rho}{\mu}\right)$ and
assume that $q\le \frac{3}{4}$. For $i,s\in \N$ and times
$t\ge 4(\Psi^s(0)+i\cdot\kappa\cdot D)/\mu$, it holds that
$$\Psi^s(t)\le \frac{\kappa D}{1-q}+q^i\left(1+\frac{\rho}{\mu}\right)\Psi^s(0).$$

Consider the series given by $x_0=(1+\rho/\mu)\Psi^s_0$,
$x_{i+1}=\kappa \cdot D + q x_i$, $t_0=0$, and
$t_{i+1}=t_i+\frac{x_i}{\mu}$. By applying
Lemma [\[lemma:psi\_bound\_same\]](#lemma:psi_bound_same){reference-type="ref"
reference="lemma:psi_bound_same"} with time $0$ replaced by time $t_i$
(i.e., shifting time) and $\Psi^s(0)$ by $x_i$, we can conclude that
$x_i$ upper bounds $\Psi^s(t)$ at times $t\ge t_i$. Simple calculations
show that $x_i\le \frac{\kappa D}{1-q}+q^i\Psi^s(0)$ and
$t_i\le 4(\Psi^s(0)+i\cdot\kappa\cdot D)/\mu$, so the claim follows.

In particular, $\Psi^s$ becomes bounded by $(1+O(\rho/\mu))\kappa D$
within $O(\Psi^s(0)/\mu)$ time. Plugging in $s=0$, we obtain a bound on
the global skew.

[\[cor:global\]]{#cor:global label="cor:global"} If
$\frac{\rho}{\mu}\cdot \left(1+\frac{\rho}{\mu}\right)\le \frac{3}{4}$,
it holds that
$$\calG(t)\le \frac{\kappa D}{1-q}+q^i\left(1+\frac{\rho}{\mu}\right)\calG(0)$$
at all times $t\ge 4(\calG(0)+i\cdot\kappa\cdot D)/\mu$.

By applying [\[cor:convergence\]](#cor:convergence){reference-type="ref"
reference="cor:convergence"} for $s=0$, noting that
$\calG(t)=\Psi^0(t)$.

Bounding the Local Skew {#sec:local-skew-bound}
-----------------------

In order to bound the local skew, we analyze the *average* skew over
paths in $G$ of various lengths. For long paths of $\Omega(D)$ hops, we
will simply exploit that we already bounded the global skew, i.e., the
skew between *any* pair of nodes. For successively shorter paths, we
inductively show that the average skew between endpoints cannot increase
too quickly: reducing the length of a path by factor $\sigma$ can only
increase the skew between endpoints by an additive constant term. Thus,
paths of constant length (in particular edges) can only have a(n
average) skew that is logarithmic in the network diameter.

In order to bound $\Psi^s$ in terms of $\Psi^{s-1}$, we need to apply
the catch-up lemma in a different form.

[\[cor:catch\_up\_different\]]{#cor:catch_up_different
label="cor:catch_up_different"} Let $s\in \Zpos$ and $t_0$, $t_1$ be
times satisfying $$t_1 \geq t_0 + \frac{\Psi^{s-1}(t_0)}{\mu}.$$ Then,
for any $w \in V$ we have
$$L_w(t_1) - L_w(t_0) \ge t_1 - t_0 + \Psi_w^s(t_0).$$

We have that $\Psi^{s-1}(t_0)\ge \Xi^{s-1}(t_0)$ and there is some
$v\in V$ satisfying $$\begin{aligned}
\Psi_w^s(t_0)&=L_v(t_0)-L_w(t_0)-2s\kappa d(v,w).\end{aligned}$$ We
apply [\[lemma:catch\_up\]](#lemma:catch_up){reference-type="ref"
reference="lemma:catch_up"} to $t_0$, $t_1$, $v$, $w$ and level $s-1$,
yielding that $$\begin{aligned}
&L_w(t_1)-L_w(t_0)\\
&\qquad\ge t_1-t_0+L_v(t_0)-L_w(t_0)-(2s-1)\kappa d(v,w)\\
&\qquad\ge t_1-t_0+L_v(t_0)-L_w(t_0)-2s\kappa d(v,w)\\
&\qquad=t_1-t_0+\Psi_w^s(t_0).\qedhere\end{aligned}$$

Combining this corollary with
[\[lemma:wait\_up\]](#lemma:wait_up){reference-type="ref"
reference="lemma:wait_up"}, we can bound $\Psi^s$ at all times.

[\[lemma:psi\_bound\_different\]]{#lemma:psi_bound_different
label="lemma:psi_bound_different"} Fix $s\in \Zpos$ and suppose that
$\Psi^{s-1}(t)\le \psi^{s-1}$ for all times $t$. Then $$\Psi^s(t)\le
\begin{cases}
\Psi^s(0)+\frac{\rho}{\mu}\cdot \psi^{s-1} & \mbox{if }t\le \frac{\psi^{s-1}}{\mu}\\
\frac{\rho}{\mu}\cdot \psi^{s-1} & \mbox{else.}
\end{cases}$$

For $t\le \psi^{s-1}/\mu$, the claim follows immediately from
[\[cor:wait\_up\]](#cor:wait_up){reference-type="ref"
reference="cor:wait_up"}. To show the claim for $t>\psi^{s-1}/\mu$,
assume for contradiction that it does not hold true and let $t_1$ be
minimal such that there $\Psi^s(t_1)>\rho \psi^{s-1}/\mu + \varepsilon$
for some $\varepsilon>0$. Thus, there is some $w\in V$ so that
$$\Psi_w^s(t_1)=\Psi^s(t_1)=\frac{\rho}{\mu}\cdot\psi^{s-1} + \varepsilon.$$
Applying
[\[cor:catch\_up\_different\]](#cor:catch_up_different){reference-type="ref"
reference="cor:catch_up_different"} with $t_0=t_1-\psi^{s-1}/\mu$
together with [\[lemma:wait\_up\]](#lemma:wait_up){reference-type="ref"
reference="lemma:wait_up"} yields the contradiction $$\begin{aligned}
\Psi^s_w(t_1)&\le \Psi^s_w(t_0)-(L_w(t_1)-L_w(t_0))+(1+\rho)(t_1-t_0)\\
&\le \rho (t_1-t_0)\\
& = \frac{\rho}{\mu}\cdot\psi^{s-1}.\qedhere\end{aligned}$$

[\[cor:local\]]{#cor:local label="cor:local"} Fix $s\in \N$. Suppose
that $\Psi^s(t)\le \psi^s$ for all times $t$ and that
$\calL(0)\le 2(s+1)\kappa$. Then
$$\Psi^{s'}(t)\le \left(\frac{\rho}{\mu}\right)^{s'-s}\psi^s$$ for all
$s'\geq s$ and times $t$.

Observe that $\calL(0)\le 2(s+1)\kappa$ implies that $\Psi^{s'}(0)=0$
for all $s'>s$. Thus, the statement follows from
[\[lemma:psi\_bound\_different\]](#lemma:psi_bound_different){reference-type="ref"
reference="lemma:psi_bound_different"} by induction on $s'$, where
$\psi^{s'}=\rho \cdot \psi^{s'-1}/\mu$ and the base case is $s'=s$.

[\[cor:local\_stab\]]{#cor:local_stab label="cor:local_stab"} Fix
$s\in \N$. Suppose that $\Psi^s(t)\le \psi^s$ for all times $t$. Then
$$\Psi^{s'}(t)\le \left(\frac{\rho}{\mu}\right)^{s'-s}\psi^s$$ for all
$s'\geq s$ and times $t\ge \psi^s/(\mu-\rho)$.

Consider the times
$$t_{s'}=\sum_{i=1}^{s'-s}\left(\frac{\rho}{\mu}\right)^i\cdot \frac{\psi^s}{\mu}\le \frac{\psi^s}{\mu}\cdot \frac{1}{1-\rho/\mu}=\frac{\psi^s}{\mu-\rho}.$$
We apply
[\[lemma:psi\_bound\_different\]](#lemma:psi_bound_different){reference-type="ref"
reference="lemma:psi_bound_different"} inductively, where in step $s'>s$
we shift times by $-t_{s'}$. Thus, all considered times fall under the
second case of
[\[lemma:psi\_bound\_different\]](#lemma:psi_bound_different){reference-type="ref"
reference="lemma:psi_bound_different"}, i.e., the initial values
$\Psi^{s'}(0)$ (or rather $\Psi^{s'}(t_{s'})$) do not matter.

Putting Things Together
-----------------------

It remains to combine the results on global and local skew to derive
bounds that depend on the system parameters and initialization
conditions only. First, we state the bounds on global and local skew
that hold at all times. We emphasize that this bound on the local skew
also bounds up to which level $s\in \N$ the algorithm needs to check
$\FT1$ and $\FT2$, as larger local skews are impossible.

[\[thm:bound\_levels\]]{#thm:bound_levels label="thm:bound_levels"}
Suppose that $\calL(0)\le (2s+1)\kappa$ for some $s\in \N$. Then
$$\begin{aligned}
\calG(t)&\le \left(2s+\frac{\mu}{\mu-\rho}\right)\kappa D\\
\mbox{and}\qquad \calL(t)&\le \left(2s+\left\lceil \log_{\mu/\rho}\frac{\mu D}{\mu-\rho}\right\rceil+1\right)\kappa\end{aligned}$$
for all $t\in \nnR$.

As $\calL(0)\le (2s+1)\kappa$, we have that
$$\Psi^s(0)\le \max_{v,w\in V}\{d(v,w)\}\cdot\kappa = \kappa \cdot D.$$
By
[\[lemma:psi\_bound\_same\]](#lemma:psi_bound_same){reference-type="ref"
reference="lemma:psi_bound_same"}, hence
$\Psi^s(t)\le \frac{\mu}{\mu-\rho}\cdot \kappa \cdot D$ at all times
$t$. Thus, $$\begin{aligned}
L_v(t)-L_w(t)-2s\kappa D &\le L_v(t)-L_w(t)-2s\kappa d(v,w)\\
&\le \Psi^s(t)\\
&\le \frac{\mu}{\mu-\rho}\cdot \kappa \cdot D\end{aligned}$$ for all
$v,w\in V$ and times $t$, implying the stated bound on the global skew.

Concerning the local skew, apply
[\[cor:local\]](#cor:local){reference-type="ref" reference="cor:local"}
with $\psi^s=\frac{\mu}{\mu-\rho}\cdot \kappa \cdot D$ and
$s'=s+\left\lceil \log_{\mu/\rho}\frac{\mu D}{\mu-\rho}\right\rceil$,
yielding that
$$\Psi^{s'}(t)\le \left(\frac{\rho}{\mu}\right)^{\lceil\log_{\mu/\rho}(\psi^s/\kappa)\rceil}\psi^s\le \kappa.$$
Hence, for all neighbors $v,w\in V$ and all times $t$, $$\begin{aligned}
L_v(t)-L_w(t)-2s'\kappa &= L_v(t)-L_w(t)-2s'\kappa d(v,w)\\
&\le \Psi^{s'}(t)\le \kappa,\end{aligned}$$ implying the claimed bound
on the local skew.

In particular, if the system can be initialized with local skew at most
$\kappa$, the system maintains the strongest bounds the algorithm
guarantees at all times.

[\[cor:perfect\_init\]]{#cor:perfect_init label="cor:perfect_init"}
Suppose that $\calL(0)\le \kappa$. Then $$\begin{aligned}
\calG(t)&\le \frac{\mu}{\mu-\rho}\cdot \kappa D\\
\mbox{and}\qquad \calL(t)&\le \left(\left\lceil \log_{\mu/\rho}\frac{\mu D}{\mu-\rho}\right\rceil+1\right)\kappa\end{aligned}$$
for all $t\in \nnR$.

If such highly accurate intialization is not possible, the algorithm
will converge to the bounds from
[\[cor:perfect\_init\]](#cor:perfect_init){reference-type="ref"
reference="cor:perfect_init"}.

[\[thm:stable\_skew\]]{#thm:stable_skew label="thm:stable_skew"} Suppose
that $\mu>2\rho$. Then there is some
$T\in O\left(\frac{\calG(0)+\kappa D}{\mu-2\rho}\right)$ such that
$$\begin{aligned}
\calG(t)&\le \frac{\mu}{\mu-2\rho}\cdot \kappa D\\
\mbox{and}\qquad \calL(t)&\le \left(\left\lceil \log_{\mu/\rho}\frac{\mu D}{\mu-2\rho}\right\rceil+1\right)\kappa\end{aligned}$$
for all times $t\ge T$.

By assumption,
$$q=\frac{\rho}{\mu}\cdot \left(1+\frac{\rho}{\mu}\right)\le \frac{1}{2}\cdot \frac{3}{2}=\frac{3}{4}.$$
Fix some sufficiently small constant $\varepsilon>0$ such that
$$\frac{\kappa D}{1-q}+\varepsilon \kappa D \le \frac{\kappa D}{1-2\rho/\mu};$$
since $q\le \frac{3}{2}\cdot\frac{\rho}{\mu}$, such a constant exists.
Choose $i\in \N$ minimal with the property that
$q^i\left(1+\frac{\rho}{\mu}\right)\calG(0)\le \varepsilon \kappa D$.
Therefore, by [\[cor:global\]](#cor:global){reference-type="ref"
reference="cor:global"}, $$\calG(t)\le \frac{\mu \kappa D}{\mu-2\rho}$$
at all times $t\ge 4(\calG(0)+i\kappa D)/\mu$. Noting that
$\Psi^0(t)=\calG(t)$, analogously to
[\[thm:bound\_levels\]](#thm:bound_levels){reference-type="ref"
reference="thm:bound_levels"} we can now apply
[\[cor:local\_stab\]](#cor:local_stab){reference-type="ref"
reference="cor:local_stab"} to infer the desired bound on the local skew
for times
$$t\ge \frac{4(\calG(0)+i\kappa D)}{\mu}+\frac{\mu \kappa D}{(\mu-\rho)(\mu-2\rho)}.$$
Consequently, it remains to show that the right hand side of this
inequality is indeed in
$O\left(\frac{\calG(0)+\kappa D}{\mu-2\rho}\right)$. As
$\mu-\rho\ge \mu/2$, this is immediate for the second term. Concerning
the first term, our choice of $i$ and $q\le 3/4$ yield that
$i\in O\left(\log \frac{\calG(0)}{\kappa D}\right)$. Because for
$x\ge y>0$ it holds that $x\ge \log(x/y)\cdot y$, we can bound
$$\frac{4(\calG(0)+i\kappa D)}{\mu}\in O\left(\frac{\calG(0)+\kappa D}{\mu-2\rho}\right).\qedhere$$

Proof of Lemma [\[lem:max-bound\]](#lem:max-bound){reference-type="ref" reference="lem:max-bound"} {#sec:max-bound}
--------------------------------------------------------------------------------------------------

We prove the stronger claim that for all $a, b$ satisfying
$t_0 \leq a < b \leq t_1$, we have
$$\frac{F(b) - F(a)}{b - a} \leq r. \label{eqn:avg-slope-bound}$$ To
this end, suppose to the contrary that there exist $a_0 < b_0$
satisfying $(F(b_0) - F(a_0)) / (b_0 - a_0) \geq r + \e$ for some
$\e > 0$. We define a sequence of nested intervals
$[a_0, b_0] \supset [a_1, b_1] \supset \cdots$ as follows. Given
$[a_j, b_j]$, let $c_j = (b_j + a_j) / 2$ be the midpoint of $a_j$ and
$b_j$. Observe that $$\begin{aligned}
  \frac{F(b_j) - F(a_j)}{b_j - a_j} &= \frac 1 2 \frac{F(b_j) - F(c_j)}{b_j - c_j} + \frac{1}{2} \frac{F(c_j) - F(a_j)}{c_j - a_j}\\
  &\geq r + \e,
  \end{aligned}$$ so that
$$\frac{F(b_j) - F(c_j)}{b_j - c_j} \geq r + \e \quad\text{or}\quad \frac{F(c_j) - F(a_j)}{c_j - a_j} \geq r + \e.$$
If the first inequality holds, define $a_{j+1} = c_j$, $b_{j+1} = b_j$,
and otherwise define $a_{j+1} = a_j$, $b_j = c_j$. From the construction
of the sequence, it is clear that for all $j$ we have
$$\label{eqn:average-slope}
    \frac{F(b_j) - F(a_j)}{b_j - a_j} \geq r + \e.$$ Observe that the
sequences $\set{a_j}_{j = 0}^\infty$ and $\set{b_j}_{j=0}^\infty$ are
both bounded and monotonic, hence convergent. Further, since
$b_j - a_j = \frac{1}{2^j}(b_0 - a_0)$, the two sequences share the same
limit.

Define $$c = \lim_{j \to \infty} a_j = \lim_{j \to \infty} b_j,$$ and
let $f \in \mathcal{F}$ be a function satisfying $f(c) = F(c)$. By the
hypothesis of the lemma, we have $f'(c) \leq r$, so that
$$\lim_{h \to 0} \frac{f(c + h) - f(h)}{h} \leq r.$$ Therefore, there
exists some $h > 0$ such that for all $t \in [c - h, c + h]$,
$t \neq c$, we have $$\frac{f(t) - f(c)}{t - c} \leq r + \frac 1 2 \e.$$
Further, from the definition of $c$, there exists $N \in \N$ such that
for all $j \geq N$, we have $a_j, b_j \in [c - h, c + h]$. In particular
this implies that for all sufficiently large $j$, we have
$$\begin{aligned}
    \frac{f(c) - f(a_j)}{c - a_j} &\leq r + \frac 1 2 \e, \label{eqn:aj-ineq}\\
    \frac{f(b_j) - f(c)}{b_j - c} &\leq r + \frac 1 2 \e. \label{eqn:bj-ineq}
  \end{aligned}$$ Since $f(a_j) \leq F(a_j)$ and
$f(c) = F(c)$, ([\[eqn:aj-ineq\]](#eqn:aj-ineq){reference-type="ref"
reference="eqn:aj-ineq"}) implies that for all $j \geq N$,
$$\frac{F(c) - F(a_j)}{c - a_j} \leq r + \frac 1 2 \e.$$ However, this
expression combined
with ([\[eqn:average-slope\]](#eqn:average-slope){reference-type="ref"
reference="eqn:average-slope"}) implies that for all $j \geq N$
$$\frac{F(b_j) - F(c)}{b_j - c} \geq r + \e. \label{eqn:bj-slope}$$
Since $F(c) = f(c)$, the previous expression together
with ([\[eqn:bj-ineq\]](#eqn:bj-ineq){reference-type="ref"
reference="eqn:bj-ineq"}) implies that for all $j \geq N$ we have
$f(b_j) < F(b_j)$.

For each $j \geq N$, let $g_j \in \mathcal{F}$ be a function such that
$g_j(b_j) = F(b_j)$. Since $\mathcal{F}$ is finite, there exists some
$g \in \mathcal{F}$ such that $g = g_j$ for infinitely many values $j$.
Let $j_0 < j_1 < \cdots$ be the subsequence such that $g = g_{j_k}$ for
all $k \in \N$. Then for all $j_k$, we have $F(b_{j_k}) = g(b_{j_k})$.
Further, since $F$ and $g$ are continuous, we have
$$g(c) = \lim_{k \to \infty} g(b_{j_k}) = \lim_{k \to \infty} F(b_{j_k}) = F(c) = f(c).$$
By ([\[eqn:bj-slope\]](#eqn:bj-slope){reference-type="ref"
reference="eqn:bj-slope"}), we therefore have that for all $k$
$$\frac{g(b_{j_k}) - g(c)}{b_{j_k} - c} = \frac{F(b_j) - F(c)}{b_j - c} \geq r + \e.$$
However, this final expression contradicts the assumption that
$g'(c) \leq r$.
Therefore, ([\[eqn:avg-slope-bound\]](#eqn:avg-slope-bound){reference-type="ref"
reference="eqn:avg-slope-bound"}) holds, as desired.

[^1]: One can account for asymmetric propagation times by shifting
    $L_w(t_w)$ and $L_v(t_v)$ accordingly, so long as this is accounted
    for in $\Tmax$ and carry out the proof analogously.

[^2]: We assume a register here, but the same argument applies to any
    state-holding component serving this purpose in the measurement
    circuit.

[^3]: For simplicity of the presentation we neglect the setup/hold time
    $\e$ (accounted for in $\delta_0$) and metastability; see
    Section [\[sec:modules\]](#sec:modules){reference-type="ref"
    reference="sec:modules"} for a discussion.
