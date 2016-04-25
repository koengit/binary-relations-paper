\documentclass{easychair}
%include polycode.fmt
\usepackage{amssymb}

% ------------------------------------------------------------------------------
% - title and stuff

\title{Dealing with Common Binary Relations in a First-Order Setting}

\author{
  Koen Claessen
  \and 
  Ann Lilliestr{\"o}m
}

\institute{
  Chalmers University of Technology
  \email{\{koen,annl\}@@chalmers.se}
}

\begin{document}

\maketitle

% ------------------------------------------------------------------------------
% - some symbols

%format flip    (r) = r "^{\smallfrown}"
%format neg     (r) = r "^{\neg{}}"
%format negflip (r) = r "^{\neg{}\smallfrown}"

%format ^^  = "^{\smallfrown}"
%format ^~  = "^{\neg{}}"
%format ^~^ = "^{\neg{}\smallfrown}"

%format <=> = "\leftrightarrow "

% ------------------------------------------------------------------------------
% - abstract

\begin{abstract}
...
\end{abstract}

% ------------------------------------------------------------------------------
% - introduction

\section{Introduction}

binary relations are common in F-O problems

how to deal with them (axiomatize, code them) is a natural question

some binary relations have built-in support in some/most theorem provers

Questions we want to help answer:

- how should certain common binary relations be expressed / coded / dealt with in a theory?

- how should certain common binary relations be dealt with in a prover?

- is it good idea to add more built-in support in provers for certain binary relations? (Good idea means: is this common enough, and is the pay-off big enough?)

The audience is both:

- writers of theories and problems

- implementors of tools

% ------------------------------------------------------------------------------
% - properties of binary relations

\section{Common properties of binary relations}

%include Implications/equivalences.tex

list of properties we use + neg + flip

table of which ones of these are equivalent

how common are these in TPTP

how common are combinations of these properties in TPTP

list of binary relations we choose to look at in this paper: equivalence relations, partial equivalence relations, total orderings, strict total orderings

table of which sets of properties imply other properties and how we computed this table

% ------------------------------------------------------------------------------
% - equivalence relations

\section{Dealing with equivalence relations}

equivalence relations

how to discover equivalence relations

how common are equivalence relations

how to encode equivalence relations + correctness proof

(partial equivalence relations

discover, how common

how to encode + proof)

% ------------------------------------------------------------------------------
% - dealing with total orderings

\section{Dealing with total orderings}

total orderings, strict total orderings

how to discover total orderings

how common are total orderings, strict total orderings

possible axiomatizations + correctness proof

encoding total orderings using ordering on the reals + proof

% ------------------------------------------------------------------------------
% - experimental results

\section{Experimental results}

\subsection{Equivalence relations}

original vs. equalified for E

original vs. equalified for Vampire

original vs. equalified for Z3

original vs. equalified for CVC4

original vs. equalified for Paradox - Satisfiable and Unsatisfiable

(original vs. p-equalified for E

original vs. p-equalified for Vampire

original vs. p-equalified for Z3

original vs. p-equalified for CVC4

original vs. p-equalified for Paradox - Satisfiable and Unsatisfiable)

\subsection{Total orderings}

total ordering vs. strict total ordering for E

total ordering vs. strict total ordering for Vampire

(total ordering/neg vs. strict total ordering/neg for E, Vampire

or some other comparisons)

total ordering vs. $\leq_\mathbb{R}$ for Z3

total ordering vs. $\leq_\mathbb{R}$ for CVC4

(Should we show

strict-total ordering vs. $\leq_\mathbb{R}$ for Z3

strict-total ordering vs. $\leq_\mathbb{R}$ for CVC4

separately? Only if the results differ.)

% ------------------------------------------------------------------------------
% - discussion and related work

\section{Discussion and Related Work}

chaining \cite{bachmair1998ordered}

...

% ------------------------------------------------------------------------------
% - conclusions and future work

\section{Conclusions and Future Work}

...

% ------------------------------------------------------------------------------
% - references

\bibliographystyle{plain}
\bibliography{main}

\end{document}
