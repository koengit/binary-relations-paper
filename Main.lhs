\documentclass{easychair}
\usepackage{amssymb}
\usepackage{mathabx}
%include polycode.fmt

% ------------------------------------------------------------------------------
% - title and stuff

\title{Dealing with Common Binary Relations\\in First-Order Automated Reasoning}

\titlerunning{Dealing with Common Binary Relations}

\author{
  Koen Claessen
  \and 
  Ann Lilliestr{\"o}m
}

\authorrunning{Claessen, Lilliestr{\"o}m}

\institute{
  Chalmers University of Technology
  \email{\{koen,annl\}@@chalmers.se}
}

\begin{document}

\maketitle

% ------------------------------------------------------------------------------
% - some symbols

%format flip    (r) = r "^{\curvearrowleftright}"
%format neg     (r) = r "^{\neg{}}"
%format negflip (r) = r "^{\neg{}\curvearrowleftright}"

%format ^^  = "^{\curvearrowleftright}"
%format ^~  = "^{\neg{}}"
%format ^~^ = "^{\neg{}\curvearrowleftright}"

%format forall = "\forall{}\hspace{-0.1cm}"
%format exists = "\exists{}\hspace{-0.1cm}"
%format .      = ".\;"
%format not    = "\neg{}\hspace{-0.1cm}"
%format ~      = "\neg{}"
%format =>     = "\Rightarrow "
%format <=>    = "\Leftrightarrow "

%format R = "R\hspace{-0.1cm}"

% ------------------------------------------------------------------------------
% - abstract

\begin{abstract}
We present a number of alternative ways of axiomatizing binary relations that commonly occur in first-order problems, in particular {\em equivalence relations} and {\em total orderings}. We show how such relations can be discovered syntactically in an input theory. We experimentally evaluate these axiomitizations on problems from the TPTP, using resolution-based reasoning tools as well as instance-based tools. Our conclusions are that (1) it is beneficial to considering different axiomatizations of binary relations as a user, and that (2) reasoning tools could benefit from using a preprocessor or even built-in support for certain binary relations.
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

\section{Common properties of binary relations} \label{sec:properties}

\begin{figure}[t]
\begin{code}
reflexive      ==  forall x             . R(x,x)
euclidean      ==  forall x,y,z         . R(x,y) && R(x,z) => R(y,z)
antisymmetric  ==  forall x,y           . R(x,y) && R(y,x) => x=y
transitive     ==  forall x,y,z         . R(x,y) && R(y,z) => R(x,z)
asymmetric     ==  forall x,y           . ~R(x,y) || ~R(y,x)
total          ==  forall x,y           . R(x,y) || R(y,x)
symmetric      ==  forall x,y           . R(x,y) => R(y,x)
coreflexive    ==  forall x,y           . R(x,y) => x=y
\end{code}
\caption{Definitions of common properties of binary relations}
\end{figure}

\begin{figure}[t]
\begin{tabular}{rl}
4945 & reflexive \\
2082 & euclidean \\
1874 & antisymmetric \\
1567 & transitive \\
784  & asymmetric \\
784  & total \\
388  & symmetric \\
3    & coreflexive \\
(163 & other)
\end{tabular}
\caption{Number of occurrences of properties in TPTP}
\end{figure}

\begin{figure}[t]
%include Implications/equivalences.tex
\caption{Properties that are equivalent}
\end{figure}

implications: described in Appendix \ref{sec:implications}.

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

% ------------------------------------------------------------------------------
% - appendix

\appendix
\section{Implications between properties} \label{sec:implications}
Here follows the complete list of implications between properties that we discovered using the method described in Sect. \ref{sec:properties}.

{\small
%{
%format <= = "\Leftarrow"
%include Implications/implications.tex
%}
}

\end{document}

