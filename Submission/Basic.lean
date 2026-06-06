% In this file you should put the actual content of the blueprint.
% It will be used both by the web and the print version.
% It should *not* include the \begin{document}
%
% If you want to split the blueprint content into several files then
% the current file can be a simple sequence of \input. Otherwise It
% can start with a \section or \chapter for instance.

\chapter{The One-Period Binomial Model for European Contingent Claims}

\section{The Market}

\begin{definition}\label{def:parameters}
    \uses{}
    The initial \emph{market parameters} are defined by
    \begin{itemize}
        \item $S_0 > 0$, the initial price of the risky asset;
        \item $u > 0$, the up factor;
        \item $d > 0$, the down factor;
        \item $r > -1$ such that the risk-free asset grows by a factor of $1 + r$ at each time step.
    \end{itemize}
    We note that $u$, $d$, and $r$ are fixed constants and the following relation must hold:
    $u > d$ as the up factor must be greater than the down factor;
\end{definition}

\begin{definition}\label{def:sample_space}
    \lean{Ω}
    \uses{def:parameters}
    The sample space for the ECC binomial model is $\Omega = \{u, d\}$, representing a single up or down move.
    We apply the probability measure $P$ such that $P(\{u\}) > 0$ and $P(\{d\}) > 0$.
\end{definition}

\begin{definition}\label{def:binomialfiltration}
    \lean{binomial_filtration}
    \leanok
    \uses{def:sample_space}
    The filtration for the ECC binomial model is the natural filtration, defined as $\mathcal{F}^0_0 = \{\emptyset, \Omega\}$ and $\mathcal{F}^0_1 = 2^\Omega$.
\end{definition}

\section{Asset Prices}

\begin{definition}\label{def:bond}
    \lean{B₀, B₁}
    \leanok
    \uses{def:parameters}
    The \emph{bond} is the risk-free asset, with price process defined by $B_0 = 1$ and $B_1 = 1 + r$.
\end{definition}

\begin{definition}\label{def:stock}
    \lean{S₁}
    \leanok
    \uses{def:parameters, def:sample_space, def:binomial_filtration}
    The \emph{stock} is the risky asset, with price process defined by $S_0$ at time 0 and
    \[
        S_1(\omega) =
        \begin{cases}
            u S_0 & \text{if } \omega = u, \\
            d S_0 & \text{if } \omega = d.
        \end{cases}
    \]
\end{definition}

\begin{definition}\label{def:trading_strategy}
    \lean{trading_strategy}
    \leanok
    \uses{def:binomial_filtration}
    A \emph{trading strategy} is a pair of $\mathcal{F}^0$-adapted processes $\varphi = (\alpha, \beta)$,
    where $\alpha_t$ represents the number of shares of the stock held at time $t$ and $\beta_t$ represents the number of shares of the bond held at time $t$.
    The value of the trading strategy at time $t$ is given by $V_t(\varphi) = \alpha_t S_t + \beta_t B_t$.
\end{definition}

\section{Arbitrage}

\begin{definition}\label{def:arbitrage}
    \lean{arbitrage}
    \leanok
    \uses{def:trading_strategy, def:bond, def:stock}
    There exists \emph{arbitrage} or equivalently an \emph{arbitrage opportunity} if there exists a trading strategy $\varphi = (\alpha, \beta)$ such that
    \begin{itemize}
        \item $V_0(\varphi) = 0$;
        \item $V_1(\varphi) \geq 0$;
        \item $E[V_1(\varphi)] > 0$.
    \end{itemize}
\end{definition}

\begin{definition}\label{def:arbitrage_free}
    \lean{arbitrage_free}
    \leanok
    \uses{def:arbitrage}
    The market is \emph{arbitrage-free} if there are no arbitrage opportunities.
\end{definition}

\begin{definition}\label{def:risk_neutral_probability}
    \lean{q}
    \leanok
    \uses{def:parameters, def:sample_space, def:binomial_filtration, def:bond, def:stock}
    A \emph{risk-neutral probability} is a probability measure $q$ on $\Omega$ such that
    \[
        q = \frac{(1 + r) - d}{u - d}
    \]
\end{definition}

\begin{lemma}\label{lem:arbitrage_free_condition}
    \lean{arbitrage_free_condition}
    \notready
    \uses{def:parameters, def:arbitrage_free}
    The market is arbitrage-free if and only if $d < 1 + r < u$.
\end{lemma}

\begin{proof}
    \begin{itemize}
        \item ($\Rightarrow$) Assume the market is arbitrage-free. If $(1 + r) \leq d$, then define the trading strategy $\varphi = (\alpha, \beta)$ by $\alpha_0 = 1$, $\beta_0 = -S_0$.
            Then $V_0(\varphi) = 0$ and $V_1(\varphi) = S_1 - S_0 (1 + r) \geq 0$ with positive probability. Thus, $E[V_1(\varphi)] > 0$, which contradicts the assumption of no arbitrage.
            Similarly, if $(1 + r) \geq u$, then define the trading strategy $\varphi = (\alpha, \beta)$ by $\alpha_0 = -1$, $\beta_0 = S_0$.
            Then $V_0(\varphi) = 0$ and $V_1(\varphi) = -S_1 + S_0 (1 + r) \geq 0$ with positive probability, leading to a similar contradiction.
        \item ($\Leftarrow$) Assume $d < 1 + r < u$. Let $\varphi = (\alpha, \beta)$ be any trading strategy such that $V_0(\varphi) = 0$. Then $\beta_0 = -\alpha_0 S_0$ and
            \[
                V_1(\varphi) =
                \begin{cases}
                    \alpha_0 S_1 + \beta_0 S_0 (1 + r) = \alpha_0 S_0(u - (1 + r)) & \text{if } \omega = u,  \\
                    \alpha_0 S_1 + \beta_0 S_0 (1 + r) = \alpha_0 S_0(d - (1 + r)) & \text{if } \omega = d.
                \end{cases}
            \]
            Since $d < 1 + r < u$, we note that $V_1(\varphi) < 0$ with positive probability, so the market is arbitrage-free.
        \end{itemize}
\end{proof}

\begin{lemma}\label{lem:q_in_unit_interval}
    \lean{q_in_unit_interval}
    \leanok
    \uses{def:risk_neutral_probability, def:parameters}
    The risk-neutral probability $q$ is in the unit interval $(0, 1)$ if and only if $d < 1 + r < u$.
\end{lemma}

\begin{proof}
    Follows directly from the definition of $q$ and the condition $d < 1 + r < u$.
\end{proof}

\begin{definition}\label{def:risk_neutral_measure}
  \lean{Q}
  \leanok
  \uses{def:risk_neutral_probability, def:sample_space}
  The \emph{risk-neutral measure} $Q$ on $\Omega = \{u, d\}$ is defined by
  $Q(\{u\}) = q$ and $Q(\{d\}) = 1 - q$.
\end{definition}

\begin{lemma}\label{lem:q_is_prob_measure}
  \lean{q_is_prob_measure}
  \uses{def:risk_neutral_measure, lem:q_in_unit_interval}
  $Q$ is a probability measure on $(\Omega, \mathcal{F})$.
\end{lemma}

\begin{proof}
  \uses{lem:q_in_unit_interval}
  We have $Q(\{u\}) + Q(\{d\}) = q + (1-q) = 1$ and both weights are in
  $(0,1)$ by \ref{lem:q_in_unit_interval}.
\end{proof}

\begin{lemma}\label{lem:discounted_stock_expectation}
  \lean{discounted_stock_expectation}
  \uses{def:risk_neutral_measure, def:stock, def:bond}
  The discounted stock price satisfies
  \[
    E^Q\!\left[\frac{S_1}{1 + r}\right] = S_0.
  \]
\end{lemma}

\begin{proof}
  \uses{def:risk_neutral_measure, def:stock, def:risk_neutral_probability}
  Direct computation:
  $E^Q[S_1/(1 + r)] = q \cdot u S_0 / (1 + r) + (1-q) \cdot d S_0 / (1 + r)
  = S_0(qu + (1-q)d)/(1 + r) = S_0 \cdot (1 + r)/(1 + r) = S_0$.
\end{proof}

\section{European Contingent Claims}

\begin{definition}\label{def:ecc}
  \lean{ECC}
  \leanok
  \uses{def:sample_space}
  A \emph{European Contingent Claim} (ECC) is a random variable
  $\Phi : \Omega \to \mathbb{R}$. We write $\Phi_u = \Phi(u)$ and
  $\Phi_d = \Phi(d)$ for its two possible payoffs.
\end{definition}

\begin{example}\label{ex:european_call}
  \uses{def:ecc, def:stock}
  The \emph{European call option} with strike $K > 0$ has payoffs
  $\Phi_u = \max(uS_0 - K, 0)$ and $\Phi_d = \max(dS_0 - K, 0)$.
\end{example}

\begin{example}\label{ex:european_put}
  \uses{def:ecc, def:stock}
  The \emph{European put option} with strike $K > 0$ has payoffs
  $\Phi_u = \max(K - uS_0, 0)$ and $\Phi_d = \max(K - dS_0, 0)$.
\end{example}

\section{Replicating Strategies}

\begin{definition}\label{def:replicating_strategy}
    \lean{replicating_strategy}
    \leanok
    \uses{def:trading_strategy, def:ecc}
    A trading strategy $\varphi = {\alpha, \beta}$ is a \emph{replicating strategy} for an ECC $\Phi$ if $V_1(\varphi) = \Phi$.
\end{definition}

\begin{theorem}\label{thm:replication_existence}
    \lean{replication_existence}
    \uses{def:replicating_strategy, lem:arbitrage_free_condition}
    Under the arbitrage-free condition, every ECC $\Phi$ has a replicating strategy.
\end{theorem}

\begin{proof}
  \uses{def:replicating_strategy, lem:arbitrage_free_condition}
  The replication conditions form a linear system in $(\alpha, \beta)$
  whose coefficient matrix has determinant $(u - d)S_0 (1 + r) \neq 0$ by
  \ref{lem:arbitrage_free_condition}. Solving by substitution yields the
  stated formulas.
\end{proof}

\section{Pricing}

\begin{theorem}\label{thm:risk_neutral_pricing}
  \lean{risk_neutral_pricing}
  \uses{thm:replication_existence, def:risk_neutral_measure,
        def:ecc, def:trading_strategy}
  The initial value of the unique replicating strategy of an ECC $\Phi$ is
  \[
    V_0 = \frac{1}{1 + r}\,E^Q[\Phi] = \frac{q\,\Phi_u + (1-q)\,\Phi_d}{1 + r}.
  \]
\end{theorem}

\begin{proof}
  \uses{thm:replication_existence, def:risk_neutral_probability,
        def:risk_neutral_measure}
  Substituting the formulas from \ref{thm:replication_existence} into
  $V_0 = \alpha S_0 + \beta$ and simplifying using $q = ((1 + r) - d)/(u - d)$
  yields $V_0 = (q\Phi_u + (1-q)\Phi_d)/(1 + r) = E^Q[\Phi]/(1 + r)$.
\end{proof}

\begin{corollary}\label{cor:call_price}
  \lean{call_price}
  \uses{thm:risk_neutral_pricing, ex:european_call}
  The arbitrage-free price of a European call option with strike $K$ is
  \[
    V_0 = \frac{q\max(uS_0-K,\,0) + (1-q)\max(dS_0-K,\,0)}{1 + r}.
  \]
\end{corollary}

\begin{corollary}\label{cor:put_call_parity}
  \lean{put_call_parity}
  \uses{thm:risk_neutral_pricing, ex:european_call, ex:european_put}
  The prices of a European call $C_0$ and put $P_0$ with the same strike
  $K$ satisfy \emph{put-call parity}:
  \[
    C_0 - P_0 = S_0 - \frac{K}{1 + r}.
  \]
\end{corollary}
