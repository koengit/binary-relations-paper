\documentclass[smallcondensed,final]{svjour3}
%\usepackage{onecolceurws} % removed by Koen because it interacts with svjour3
%\usepackage{subcaption} % removed by Koen because svjour3 complained
\usepackage{anyfontsize} % added by Koen because some font sizes were not available
\usepackage{amssymb}
\usepackage{mathabx}
\usepackage{graphicx}
\usepackage{multirow}
%include polycode.fmt

\def\comment#1{$\Rightarrow$ {\em #1} $\Leftarrow$}

%\renewcommand{\paragraph}[1]{\vspace{0.2cm}\noindent {\bf #1} $\;\;$}

% ------------------------------------------------------------------------------
% - title and stuff

\journalname{Journal of Automated Reasoning}

\title{Handling Transitive Relations\\in First-Order Automated Reasoning}

\titlerunning{Handling Transitive Relations}

\author{
  Koen Claessen
  \and 
  Ann Lilliestr{\"o}m
}

\authorrunning{Claessen, Lilliestr{\"o}m}

\institute{
  Chalmers University of Technology, Gothenburg, Sweden,
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

%format §      = " "
%format **     = "\times"
%format RR     = "\mathbb{R}"
%format QQ     = "\mathbb{Q}"
%format -->    = "~~~~~\rightarrowtriangle~~~~~"

%format P  = "P\hspace{-0.1cm}"
%format P_ = "P"

%format R   = "R\hspace{-0.1cm}"
%format R1_ = "R_1"
%format R2_ = "R_2"
%format R_  = "R"

%format Q  = "Q\hspace{-0.1cm}"
%format Q_ = "Q"

%format rep  = "rep\hspace{-0.1cm}"
%format rep_ = "rep"
%format repinv  = "rep^{-1}\hspace{-0.1cm}"
%format repinv_ = "rep^{-1}"

%format max  = "max\hspace{-0.1cm}"
%format max_ = "max"

%format prop1 = prop"_1"
%format propa = prop"_a"
%format propb = prop"_b"
%format propn = prop"_n"

%format a0 = a"_0"
%format a1 = a"_1"
%format a2 = a"_2"
%format ai = a"_i"
%format an = a"_n"

% ------------------------------------------------------------------------------
% - abstract

\begin{abstract}
We present a number of alternative ways of handling transitive binary relations that commonly occur in first-order problems, in particular {\em equivalence relations}, {\em total orders}, and {\em transitive relations}. We show how such relations can be discovered syntactically in an input theory. We experimentally evaluate different treatments on problems from the TPTP, using resolution-based reasoning tools as well as instance-based tools. Our conclusions are that (1) it is beneficial to consider different treatments of binary relations as a user, and that (2) reasoning tools could benefit from using a preprocessor or even built-in support for certain types of binary relations.
\end{abstract}

% ------------------------------------------------------------------------------
% - introduction

\section{Introduction}

Most automated reasoning tools for first-order logic have some kind of built-in support for reasoning about equality. Equality is one of the most common binary relations, and there are great performance benefits from providing built-in support for equality. Together, these clearly motivate the cost of implementation.

Other common concepts for which there exists built-in support in many tools are associative, commutative operators; and real-valued, rational-valued, and integer-valued arithmetic. Again, these concepts seem to appear often enough to warrant the extra cost of implementing special support in reasoning tools.

This paper is concerned with investigating what kind of special treatment we could give to commonly appearing transitive binary relations, and what effect this treatment has in practice. Adding special treatment of transitive relations to reasoning tools has been the subject of study before, in particular by means of {\em chaining} \cite{chaining}. The transitivity axiom
\begin{code}
forall x,y,z . R(x,y) && R(y,z) => R(x,z)
\end{code}
can lead to an expensive proof exploration in resolution and superposition based theorem provers, and can generate a huge number of instances in instance-based provers and SMT-solvers. Transitive relations are also common enough to motivate special built-in support. However, as far as we know, chaining is not implemented in any of the major first-order reasoning tools (at least not in E \cite{E}, Vampire \cite{Vampire}, Z3 \cite{Z3}, and CVC4 \cite{CVC4}, which were used in this paper).

As an alternative to adding built-in support, in this paper we mainly look at (1) what a user of a reasoning tool may do herself to optimize the handling of these relations, and (2) how a preprocessing tool may be able to do this automatically. Adding built-in reasoning support in the tools themselves is not a main concern of this paper.

By ``treatment'' we mean any way of logically expressing the relation. For example, a possible treatment of a binary relation |R_| in a theory |T| may simply mean axiomatizing |R_| in |T|. But it may also mean transforming |T| into a satisfiability-equivalent theory |T'| where |R_| does not even syntactically appear.

As an example, consider a theory |T| in which an equivalence relation |R_| occurs. One way to deal with |R_| is to simply axiomatize it, by means of reflexivity, symmetry, and transitivity:
\begin{code}
forall x      . R(x,x)
forall x,y    . R(x,y) => R(y,x)
forall x,y,z  . R(x,y) && R(y,z) => R(x,z)
\end{code}
Another way is to ``borrow'' the built-in equality treatment that exists in most theorem provers. We can do this by introducing a new symbol |rep_|, and replacing all occurrences of |R(x,y)| by the formula:
\begin{code}
rep(x)=rep(y)
\end{code}
The intuition here is that |rep_| is now the representative function of the relation |R_|. No axioms are needed. As we shall see, this alternative treatment of equivalence relations is satisfiability-equivalent with the original one, and actually is beneficial in practice in certain cases.

In general, when considering alternative treatments, we strive to make use of concepts already built-in to the reasoning tool in order to express other concepts that are not built-in.

For the purpose of this paper, we have decided to focus on three different kinds of transitive relations: (1) {\em equivalence relations} and {\em partial equivalence relations}, (2) {\em total orders} and {\em strict total orders}, and (3) general {\em transitive relations} and {\em reflexive, transitive relations}. The reason we decided to concentrate on these three are because (a) they appear frequently in practice, and (b) we found well-known ways but also novel ways of dealing with these.

The target audience for this paper is thus both people who use reasoning tools and people who implement reasoning tools.

\paragraph{Related Work} Chaining \cite{chaining} is a family of methods that limit the use of transitivity-like axioms in proofs by only allowing certain chains of them to occur in proofs. The result is a complete proof system that avoids the derivation of unnecessary consequences of transitivity. However, chaining is not implemented in any of the reasoning tools we considered for this paper. In personal communication with some of the authors, chaining-like techniques have not been deemed important enough to be considered for implementation, and their preliminary experimental results were mostly negative.

% ------------------------------------------------------------------------------
% - properties of binary relations

\section{Common properties of binary relations} \label{sec:properties}

In this section, we take a look at commonly occurring properties of binary relations, which combinations of these are interesting for us to treat specially, and how we may go about discovering these.

\begin{figure}[t]
\begin{center}
\begin{code}
reflexive      ==  forall x      . R(x,x)
euclidean      ==  forall x,y,z  . R(x,y) && R(x,z) => R(y,z)
antisymmetric  ==  forall x,y    . R(x,y) && R(y,x) => x=y
transitive     ==  forall x,y,z  . R(x,y) && R(y,z) => R(x,z)
asymmetric     ==  forall x,y    . ~R(x,y) || ~R(y,x)
total          ==  forall x,y    . R(x,y) || R(y,x)
symmetric      ==  forall x,y    . R(x,y) => R(y,x)
coreflexive    ==  forall x,y    . R(x,y) => x=y
\end{code}
\end{center}
\vspace{-0.5cm}
\caption{Definitions of basic properties of binary relations}
\label{fig:props}
\end{figure}

Take a look at Fig.\ \ref{fig:props}. It lists 8 basic and common properties of binary relations. Each of these properties can be expressed using one logic clause, which makes it easy to syntactically identify the presence of such a property in a given theory.

\begin{figure}[t]
\begin{center}
\begin{tabular}{rl}
6598 & reflexive \\
2976 & transitive \\
2483 & antisymmetric \\
2136 & euclidean \\
2108 & total \\
2108 & asymmetric \\
1487 & symmetric \\
80 & coreflexive \\
(163 & other)
\end{tabular}
\end{center}
\vspace{-0.5cm}
\caption{Number of occurrences of binary relation properties in TPTP}
\label{fig:occurs}
\end{figure}

When we investigated the number of occurrences of these properties in a subset of the TPTP problem library (v7.0.0)\footnote{For the statistics in this paper, we decided to only look at unsorted TPTP problems with 10.000 clauses or less.} \cite{tptp}, we ended up with the table in Fig.\ \ref{fig:occurs}. The table was constructed by gathering all clauses from all TPTP problems (after clausification), and keeping every clause that only contained one binary relation symbol and, possibly, equality. Each such clause was then categorized as an expression of a basic property of a binary relation symbol. We found only 163 such clauses that did not fit any of the 8 properties we chose as basic properties, but were instead instances of two new properties. Both of these were quite esoteric and did not seem to have a standard name in mathematics.

The table also contains occurrences where a {\em negated relation} was stated to have a certain property, and also occurrences where a {\em flipped relation} (a relation with its arguments swapped) was stated to have a certain property, and also occurrences of combined negated and flipped relations. This explains for example why the number of occurrences of {\em total} relations is the same as for {\em asymmetric} relations; if a relation is total, the negated relation is asymmetric and vice-versa.

We adopt the following notation. Given a property of binary relations |prop|, we introduce its {\em negated version}, which is denoted by |prop^~|. The property |prop^~| holds for |R_| if and only if |prop| holds for |~R_|. Similarly, we introduce the {\em flipped version} of a property |prop|, which is denoted by |prop^^|. The property |prop^^| holds for |R_| if and only if |prop| holds for the flipped version of |R_|.

Using this notation, we can for example say that |total| is equivalent with |asymmetric^~|. Sometimes the property we call |euclidean| here is called |right euclidean|; the corresponding variant |left euclidean| can be denoted |euclidean^^|. Note that |prop^~| is not the same as |~prop|! For example, a relation |R_| can be |reflexive|, or |reflexive^~| (which means that |~R_| is reflexive), or |~reflexive|, which means that |R_| is not reflexive.

Using this notation on the 8 original basic properties from Fig.\ \ref{fig:props}, we end up with 32 new basic properties that we can use. (However, as we have already seen, some of these are equivalent to others.)

This paper will look at 6 kinds of different binary relations, which are defined as combinations of basic properties:
\begin{code}
equivalence relation            ==  {reflexive, symmetric, transitive}
partial equivalence relation    ==  {symmetric, transitive}
total order                     ==  {total, antisymmetric, transitive}
strict total order              ==  {antisymmetric^~, asymmetric, transitive}
transitive relation             ==  {transitive}
reflexive, transitive relation  ==  {reflexive, transitive}
\end{code}
As a side note, in mathematics, strict total orders are sometimes defined using a property called {\em trichotomous}, which means that exactly one of |R(x,y)|, |x=y|, or |R(y,x)| must be true. However, when you clausify this property in the presence of transitivity, you end up with |antisymmetric^~| which says that at least one of |R(x,y)|, |x=y|, or |R(y,x)| must be true. There seems to be no standard name in mathematics for the property |antisymmetric^~|, which is why we use this name.

% \comment{Should I include sat/csat/unknown/open in the table?}
\begin{figure}[t]
\begin{center}
\begin{tabular}{rl}
500+48 & equivalence relations \\
154+2 & partial equivalence relations \\
250+4 & (strict) total orders \\
806+15 & reflexive, transitive relations (excluding the above) \\
1128+69 & transitive relations (excluding the above) \\
\end{tabular}
\end{center}
\vspace{-0.5cm}
\caption{Number of occurrences of binary relations in TPTP, divided up into Theorem/Unsatisfiable/Unknown/Open problems + Satisfiable/CounterSatisfiable problems. }
\label{fig:occurs2}
\end{figure}

In Fig.\ \ref{fig:occurs2}, we display the number of binary relations we have found in (our subset of) the TPTP for each category. The next section describes how we found these.

% ------------------------------------------------------------------------------
% - discovering relations

\section{Syntactic discovery of common binary relations} \label{sec:discovery}

Our goal is to automatically choose the right treatment of equivalence relations, total orders, and general transitive relations. Thus, we must have an automatic way of identifying these relations in a given theory. It is relatively easy to discover for example an equivalence relation in a theory by means of syntactic inspection. If we find the presence of the axioms |reflexive|, |symmetric|, and |transitive|, for the same relational symbol |R_|, we know that |R_| is an equivalence relation.

But, there are many other ways of axiomatizing equivalence relations. For example, a much more common way to axiomatize equivalence relations in the TPTP is to state the two properties |reflexive| and |euclidean| for |R_|.
%\footnote{A possible reason for this is a paper written in the 1990s that argued for this alternative axiomatization. The first author of this paper has at one point seen this paper, but at the time of the writing, we have not been able to find it again! If any reviewer knows which paper we are talking about, help would be appreciated.}

Rather than enumerating all possible ways to axiomatize certain relations by hand, we wrote a program that computes all possible ways for any combination of basic properties to imply any other combination of basic properties. Our program generates a table that can be precomputed in a minute or so and then used to very quickly detect any alternative axiomatization of binary relations using basic properties.

\begin{figure}[t]
\begin{center}
%include Implications/equivalences.tex
\end{center}
\vspace{-0.5cm}
\caption{Basic properties that are equivalent}
\label{fig:equivs}
\end{figure}

Let us explain how this table was generated. We start with a list of 32 basic properties (the 8 original basic properties, plus their negated, flipped, and negated flipped versions). Firstly, we use an automated theorem prover (we used E \cite{E}) to discover which of these are equivalent with other such properties. The result is displayed in Fig.\ \ref{fig:equivs}. Thus, 17 basic properties can be removed from the list, because they can be expressed using other properties. The list of basic properties now has 15 elements left.

\begin{figure}
\begin{center}
{\scriptsize
%{
%format <= = "\Leftarrow"
%include Implications/implications2.tex
%}
}
\end{center}
\caption{The complete list of implications between properties}
\label{fig:imps}
\end{figure}

Secondly, we want to generate all implications of the form |{prop1, .., propn} => prop| where the set |{prop1, .., propn}| is minimal. We do this separately for each |prop|. The results are displayed in Fig.\ \ref{fig:imps}.

The procedure uses a simple constraint solver (a SAT-solver) to keep track of all implications it has tried so far, and consists of one main loop. At every loop iteration, the constraint solver guesses a set |{prop1, .., propn}| from the set of all properties |P-{prop}|. The procedure then asks E whether or not |{prop1, .., propn} => prop| is valid. If it is, then we look at the proof that E produces, and print the implication |{propa, .., propb} => prop|, where |{propa, .., propb}| is the subset of properties that were used in the proof. We then also tell the constraint solver never to guess a superset of |{propa, .., propb}| again. If the guessed implication can not be proven, we tell the constraint solver to never guess a subset of |{prop1, .., propn}| again. The procedure stops when no guesses that satisfy all constraints can be made anymore.

After the loop terminates, we may need to clean up the implications somewhat because some implications may subsume others.

In order to avoid generating inconsistent sets |{prop1, .., propn}| (that would imply any other property), we also add the artificial inconsistent property |false| to the set, and generate implications for this property first. We exclude any found implication here from the implication sets of the real properties. 

This procedure generates a complete list of minimal implications. It works well in practice, especially if all guesses made by the SAT-solver are maximized according to their size. The vast majority of the time is spent on the implication proofs, and no significant time is spent in the SAT-solver.

To detect a binary relation |R_| with certain properties in a given theory, we simply gather all basic properties about |R_| that occur in the theory, and then compute which other properties they imply, using the pre-generated table. % TODO the below text is new, Koen please read  
Also, certain properties can be derived for a binary relation |R2_| if |R2_| is implied by another binary relation |R1_|, and |R1_| has that property. This holds for reflexivity, totality and seriality. Similarly, if |R2_| is antisymmetric or coreflexive, the same property can be derived for |R1_|. When having derived a new property of a relation in this way, we iterate the procedure of finding implied properties using the precomputed table until no new information is gained.  In this way, we never have to do any actual theorem proving in order to detect a binary relation with certain properties. 

In the following three sections, we describe how to deal with equivalence relations, total orders, and general transitive relations, respectively.

% ------------------------------------------------------------------------------
% - equivalence relations

\section{Handling equivalence relations}

\paragraph{Equalification} As mentioned in the introduction, an alternative way of handling equivalence relations |R_| is to create a new symbol |rep_| and replace all occurrences of |R_| with a formula involving |rep_|:
\begin{code}
R_ reflexive     §    
R_ symmetric     -->   §
R_ transitive    §
T[.. R(x,y) ..]  §     T[.. rep(x)=rep(y) ..]
\end{code}
To explain the above notation: We have two theories, one on the left-hand side of the arrow, and one on the right-hand side of the arrow. The proposed transformation transforms any theory that looks like the left-hand side into a theory that looks like the right-hand side. We write |T[.. e ..]| for theories in which |e| occurs syntactically; in the transformation, all occurrences of |e| should be replaced.

We call the above transformation {\em equalification}. This transformation may be beneficial because reasoning about the equivalence relation now involves built-in equality reasoning instead of reasoning about an unknown symbol using axioms.

The transformation is correct, meaning that it preserves (non-)satisfiability: ($\Rightarrow$) If we have a model of the LHS theory, then |R_| must be interpreted as an equivalence relation. Let |rep_| be the representative function of |R_|, in other words we have |R(x,y) <=> rep(x)=rep(y)|. Thus we also have a model of the RHS theory. ($\Leftarrow$) If we have a model of the RHS theory, let |R(x,y):=rep(x)=rep(y)|. It is clear that |R_| is reflexive, symmetric, and transitive, and therefore we have model of the LHS theory.

In the transformation, we also remove the axioms for reflexivity, symmetry, and transitivity, because they are not needed anymore. But what if |R_| is axiomatized as an equivalence relation using different axioms? Then we can remove any axiom about |R_| that is implied by reflexivity, symmetry, and transitivity. Luckily we have already computed a table of which properties imply which other ones (shown in Fig.\ \ref{fig:imps}).

\paragraph{Pequalification} There are commonly occurring binary relations called {\em partial equivalence relations} that almost behave as equivalence relations, but not quite. In particular, they do not have to obey the axiom of reflexivity. Can we do something for these too?

A set with a partial equivalence relation |R_| can be partitioned into two subsets: (1) one subset on which |R_| is an actual equivalence relation, and (2) one subset of elements which are not related to anything, not even themselves.

Thus, an alternative way of handling partial equivalence relations |R_| is to create two new symbols, |rep_| and |P_|, and replace all occurrences of |R_| with a formula involving |rep_| and |P|:
\begin{code}
R_ symmetric     §  
R_ transitive    -->   §
T[.. R(x,y) ..]  §     T[.. (P(x) && P(y) && rep(x)=rep(y)) ..]
\end{code}
Here, |P_| is the predicate that indicates the subset on which |R_| behaves as an equivalence relation.

We call this transformation {\em pequalification}. This transformation may be beneficial because the reasoning now involves built-in equality reasoning instead of reasoning about an unknown symbol using axioms. However, there is also a clear price to pay since the size of the problem grows considerably.

The transformation is correct, meaning that it preserves (non-)satisfiability: ($\Rightarrow$) If we have a model of the LHS theory, then |R_| must be interpreted as a partial equivalence relation. Let |P(x):=R(x,x)|, in other words |P_| is the subset on which |R_| behaves like an equivalence relation. Let |rep_| be a representative function of |R_| on |P_|, in other words we have |(P(x) && P(y)) => (R(x,y) <=> rep(x)=rep(y))|. By the definition of |P_| we then also have |R(x,y) <=> (P(x) && P(y) && rep(x)=rep(y))|. Thus we also have a model of the RHS theory. ($\Leftarrow$) If we have a model of the RHS theory, let |R(x,y):=P(x) && P(y) && rep(x)=rep(y)|. This |R_| is symmetric and transitive, and therefore we have model of the LHS theory.
% TODO the below text is new, Koen please read  
Intuitively, one can see that this transformation is correct by realising that the elements on which the relation |R_| is not reflexive cannot be related to any other elements. This is because |R(x,y)| together with symmetry and transitivity gives us |R(x,x)|. Thus, when we encounter |R(x,y)| in the LHS theory, we know that both x and y are in the set defined by |P_|. (This holds also when x equals y). Since |R_| is an equivalence relation on this set, we can use the transformation of pure equivalence relations on the subset |P_| to get |P(x) && P(y) => rep(x) = rep(y)|.



% ------------------------------------------------------------------------------
% - dealing with total orders

\section{Handling total orders}

\paragraph{Ordification} Many reasoning tools have built-in support for arithmetic, in particular they support an order |<=| on numbers. It turns out that we can ``borrow'' this operator when handling general total orders. Suppose we have a total order:
\begin{code}
R_ : A ** A -> Bool
\end{code}
We now introduce a new injective function:
\begin{code}
rep_ : A -> RR
\end{code}
We then replace all occurrences of |R_| with a formula involving |rep_| in the following way:
\begin{code}
R_ total          §
R_ antisymmetric  -->   rep_ injective
R_ transitive     §
T[.. R(x,y) ..]   §     T[.. rep(x)<=rep(y) ..]
\end{code}
(Here, |<=| is the order on reals.) We call this transformation {\em ordification}. This transformation may be beneficial because the reasoning now involves built-in arithmetic reasoning instead of reasoning about an unknown symbol using axioms.

The above transformation is correct, meaning that it preserves (non-)satisfiability: ($\Rightarrow$) If we have a model of the LHS theory, then without loss of generality (by L{\"o}wenheim-Skolem), we can assume that the domain is countable. Also, |R_| must be interpreted as a total order. We now construct |rep_| recursively as a mapping from the model domain to |RR|, such that we have |R(x,y) <=> rep(x)<=rep(y)|, in the following way. Let |{a0, a1, a2, ..}| be the domain of the model, and set |rep(a0):=0|. For any |n>0|, pick a value for |rep(an)| that is consistent with the total order |R_| and all earlier domain elements |ai|, for |0 <= i < n|. This can always be done because there is always extra room for a new, unique element between any two distinct values of |RR|. Thus |rep_| is injective and we also have a model of the RHS theory. ($\Leftarrow$) If we have a model of the RHS theory, let |R(x,y):=rep(x)<=rep(y)|. It is clear that |R_| is total and transitive, and also antisymmetric because |rep_| is injective, and therefore we have model of the LHS theory.

\paragraph{Note on |QQ| vs. |RR|} The proof would have worked for |QQ| as well instead of |RR|. The transformation can therefore be used for any tool that supports |QQ| or |RR| or both, and should choose whichever comparison operator is cheapest if there is a choice. Using integer arithmetic would however not have been correct.

\paragraph{Note on injectivity} The transformation requires an axiom that expresses that |rep_| is injective. There are two natural ways in which this can be expressed. Here is a direct axiom:
\begin{code}
forall x,y. rep(x)=rep(y) => x=y
\end{code}
And here is an axiom that makes use of a helper function |repinv_| which plays the role of |rep_|s inverse:
\begin{code}
forall x. repinv(rep(x))=x
\end{code}
These two are logically equivalent. %TODO: say which one works better

\paragraph{Note on strict total orders} One may have expected to have a transformation specifically targeted to strict total orders, i.e. something like:
\begin{code}
R_ antisymmetric^~  §          
R_ asymmetric       -->   rep_ injective
R_ transitive       §
T[.. R(x,y) ..]     §     T[.. rep(x)<rep(y) ..]
\end{code}
However, the transformation for total orders already covers this case! Any strict total order |R_| is also recognized as a total order |~R_|, and ordification already transforms such theories in the correct way. The only difference is that |R(x,y)| is replaced with |~(rep(x)<=rep(y))| instead of |rep(x)<rep(y)|, which is satisfiability-equivalent. (We found no performance difference in practice between these choices.)

\paragraph{Maxification} Some reasoning tools do not have orders on real arithmetic built-in, but they may have other concepts that are built-in that can be used to express total orders instead. One such concept is handling of associative, commutative (AC) operators.

For such a tool, one alternative way of handling total orders |R_| is to create a new function symbol |max_| and replace all occurrences of |R_| with a formula involving |max_|:
\begin{code}
R_ total          §     max_ associative
R_ antisymmetric  -->   max_ commutative
R_ transitive     §     forall x,y . max(x,y)=x || max(x,y)=y
T[.. R(x,y) ..]   §     T[.. max(x,y)=y ..]
\end{code}
We call this transformation {\em maxification}. This transformation may be beneficial because the reasoning now involves built-in equality reasoning with AC unification (and one extra axiom) instead of reasoning about an unknown relational symbol (using three axioms).

The above transformation is correct, meaning that it preserves (non-)satisfiability: ($\Rightarrow$) If we have a model of the LHS theory, then |R_| must be interpreted as a total order. Let |max_| be the maximum function associated with this order. Clearly, it must be associative and commutative, and the third axiom also holds. Moreover, we have  |R(x,y) <=> max(x,y)=y|. Thus we also have a model of the RHS theory. ($\Leftarrow$) If we have a model of the RHS theory, let |R(x,y):=max(x,y)=y|. Given the axioms in the RHS theory, |R_| is total, antisymmetric, and transitive, and therefore we have model of the LHS theory.

% ------------------------------------------------------------------------------
% - detransification

\section{Handling transitive relations}

The treatments introduced so far all make use of built-in concepts of the reasoning tool, and they can be applied only to special cases of transitive relations. In this section we propose a more general approach, in which theories with a transitivity axiom are transformed into theories without that transitivity axiom. To this end, transitivity is specialized at each {\em positive occurrence} of the relational symbol. Such transformations may be beneficial because reasoning about transitivity in a naive way can be very expensive for theorem provers, because from transitivity there are many possible conclusions to draw that trigger each other ``recursively''.

The transformations presented in this subsection only work on problems where every occurrence of |R_| is either positive or negative (and not both, such as under an equivalence operator). If this is not the case, the problem has to be translated into one where this is the case. This can for example be done by means of clausification.

\paragraph{Detransification} 
A general way of handling any transitive relation |R_| is to create a new symbol |Q_| and replace all positive occurrences of |R_| with a formula involving |Q_| (see below); the negative occurrences are simply replaced by |~Q_|:
\begin{code}
R_ transitive       §   
T[..  R(x,y)   ..   -->   T[..  ( Q(x,y) && (forall r . Q(r,x) => Q(r,y)) )  ..
      ~R(x,y)  ..]  §           ~Q(x,y)                                      ..]
\end{code}
We call this transformation {\em detransification}. It can be applied to any theory that involves a transitivity axiom. The transformation removes the transitivity, but adds for every positive occurrence of |R(x,y)| an implication that says ``for any |r|, if you could reach |x| from |r|, now you can reach |y| too''. Thus, we have specialized the transitivity axiom for every positive occurrence of |R_|.

Note that in the RHS theory, |Q_| does not have to be transitive! Nonetheless, the transformation is correct, meaning that it preserves (non-)satisfiability: ($\Rightarrow$) If we have a model of the LHS theory, then |R_| is transitive. Now, set |Q(x,y) := R(x,y)|. We have to show that |R(x,y)| implies |Q(x,y)|, which is trivial, and |forall r . Q(r,x) => Q(r,y)|, which is indeed the case because |R_| is transitive. Thus we also have a model of the RHS theory. ($\Leftarrow$) Assume we have a model of the RHS theory. Now, set |R(x,y) := Q(x,y) && forall r . Q(r,x) => Q(r,y)|. We have to show that |~Q(x,y)| implies |~R(x,y)|, which is the same as showing that |Q(x,y) && forall r . Q(r,x) => Q(r,y)| implies |Q(x,y)|, which then becomes trivial. |R_| is also transitive (by transitivity of implication). Thus we also have a model of the LHS theory. 

Detransification can be seen as performing one resolution step with each positive occurrence of the relation and the transitivity axiom. A positive occurrence |R(a,b)| of a transitive relation |R_|, resolved with the transitivity axiom |R(x,y) & R(y,z) => R(x,z)| becomes |R(x,a) => R(x,b)| under the substitution y := a, z := b.

\paragraph{Detransification with reflexivity} Detransification can be simplified for transitive relations that are also reflexive. In particular, we can simplify the formula with which we replace positive occurrences of the relation symbol |R_|:
\begin{code}
R_ reflexive        §     Q_ reflexive
R_ transitive       -->   
T[..  R(x,y)   ..   §     T[..  (forall r . Q(r,x) => Q(r,y))  ..
      ~R(x,y)  ..]  §           ~Q(x,y)                        ..]
\end{code}
We now {\em replace} any positive occurrence of |R(x,y)| with an implication that says ``for any |r|, if you could reach |x| from |r|, now you can reach |y| too''. Thus, we have specialized the transitivity axiom for every positive occurrence of |R_|. The part that we leave out here (namely |Q(x,y)|) is implicitly implied by the fact that |R_| is reflexive.

Similarly to the transification transformation above, |Q_| does not have to be transitive in the RHS theory. Nonetheless, the transformation is correct, meaning that it preserves (non-)satisfiability: ($\Rightarrow$) If we have a model of the LHS theory, then |R_| is reflexive and transitive. Now, set |Q(x,y) := R(x,y)|. |Q_| is obviously reflexive. We have to show that |R(x,y)| implies |forall r . Q(r,x) => Q(r,y)|. This is indeed the case because |R_| is transitive. Thus we also have a model of the RHS theory. ($\Leftarrow$) If we have a model of the RHS theory, then |Q_| is reflexive. Now, set |R(x,y) := forall r . Q(r,x) => Q(r,y)|. |R_| is reflexive (by reflexivity of implication) and transitive (by transitivity of implication). Finally, we have to show that |~Q(x,y)| implies |~R(x,y)|, which is the same as showing that |forall r . Q(r,x) => Q(r,y)| implies |Q(x,y)|, which is true because |Q_| is reflexive. Thus we also have a model of the RHS theory. 

% ------------------------------------------------------------------------------
% - experimental results




%KOEN: what tptp version did you use to generate the lagom stora problems?

\section{Experimental results}
We evaluate the effects of the different axiomatizations using three different resolution based theorem provers, E 2.0 \cite{E} (with the \textit{xAuto} and \textit{tAuto} options), Vampire 4.0 \cite{Vampire} (with the \textit{casc mode} option), Spass 3.9 \cite{spass}  (with the \textit{Auto} option, which activates chaining in the presence of transitive predicates), and two SMT-solvers, Z3 4.5 \cite{Z3} and CVC4 1.5 \cite{CVC4}. The experiments were performed on a 2xQuad Core Intel Xeon E5620 processor with 24 GB physical memory, running at 2.4 GHz. We use a time limit of 5 minutes on each problem.
%NOT TRUE ANYMORE:
%For Vampire, no time limit is passed directly to the theorem prover but instead the process is terminated once the time limit has passed. This was done to keep solving times more stable, since Vampire uses %the time limit to control its search strategies.

We started from a set of 13410 test problems from the TPTP, listed as Unsatisfiable, Theorem or Unknown or Open (leaving out the very large theories). For each problem, a new theory was generated for each applicable transformation. For most problems, no relation matching any of the given criteria was detected, and thus no new theories were produced for these problems. In total, 2007 problems were found to include one or more transitive relations and could thus be used with at least one of the presented transformations. 130 of these problems are listed as Unknown, and an additional 172 problems have rating 1.0. No problem in the resulting set of problems is listed as Open.
Evaluation of reasoning tools on Satisfiable and CounterSatisfiable problems is left as future work. %TODO: not future work anymore(?)

The experimental results are summarized in Fig. \ref{fig:overview}.

\begin{figure}[h!]
\setlength{\tabcolsep}{5.2pt}
\begin{tabular}{lr||rrr||rrr||rrr}
  & & \multicolumn{3}{c||}{E} & \multicolumn{3}{c||}{Vampire} & \multicolumn{3}{c}{Spass} \\
\hline 
&&&&&&&&&&\\  
equalification & (436) & 427 & +5  & -38 & 434 & +0  & -7 & 385 & +16 & -46\\
\hspace{0.1cm}with idempotency &   &   &  +4  & -56 &  & +0  & -6 &   & +14 & -43\\&&&&&&&&&\\
pequalification & (617) & 524 & +5 & -69 & 526 &  +5 & -8 & 452 & +18 & -48\\
%\hspace{0.2cm}on EQ & (436) & 427 & +5 & -33 & 451 & +0 & -2 & 388 & +16 &-46 \\
%\hspace{0.2cm}on PEQ & (181) & 97 & +0 & -36 & 92 & +5 & -6 & 67 & +2 & -2  \\
\hspace{0.1cm}with idempotency &  &  &  +3  & -95  &  &  +6 & -13 & & +16 & -45\\&&&&&&&&&\\
%\hspace{0.3cm}on EQ & (436) & 427 & +3 & -59 & 451 &+0& -7 & 388 & +14 & -40 \\
%\hspace{0.3cm}on PEQ & (181) & 97 & +0 & -36 & 92 & +6 & -6 & 67 &+2 & -5 \\&&&&&&&&&\\
ordification & (326) & 272 & n/a & n/a & 295 &  +1& -0 & 243 & n/a & n/a\\&&&&&&&&&\\
detransification  & (2007) & 1483 & \bf{+15} & -101 & 1542 &  \bf{+38} & -21 & 1200 & +88 & -90\\
%\hspace{0.2cm}on EQ& (436) & 427 & +4 & -24 & 451 & +0 & -0& 388& +15 & -32 \\
%\hspace{0.2cm}on PEQ& (181) &97&\bf{+1}&-8&92&+5&-0&67 &+8 & -0\\
%\hspace{0.2cm}on TO& (326) &272&+2&-25&296&+0&-2&243&+9 & -34\\
%\hspace{0.2cm}on R& (1359)&1025&+10&-69&1062&\bf{+33}&-10&869& +40&-81\\
%\hspace{0.2cm}on R\textsuperscript{C} & (1359)&1025&+10&-69&1062&\bf{+33}&-10&869& +40&-81\\

\hspace{0.1cm}with reflexivity & (1359) & 1025 & +6 & -89 & 1062 &  \bf{+32} & -0 &866 & +29 & -90\\
%\hspace{0.3cm}on EQ & (436) & 427&+3&-30&434&+0&-0&385&+14&-44\\
%\hspace{0.3cm}on TO & (326 )& 272&+2&-34&296&+0&-0&243&+5&-31\\
\vspace{0.3cm}
\end{tabular}
%\end{center}
%\vspace{-0.5cm}

%\setlength{\tabcolsep}{5.2pt}
\begin{tabular}{lr||rrr||rrr}
  & & \multicolumn{3}{c||}{Z3} &\multicolumn{3}{c}{CVC4}  \\
\hline 
&&&&&&&\\
equalification & (436) & 354 & +60 & -7 & 370 & +35 & -20\\
\hspace{0.1cm}with idempotency &   &   & +59  & -11 &  & +35 & -22\\&&&&&&\\

pequalification & (617) & 392  &  +66  & -8  & 343  & +45 & -25\\

%\hspace{0.2cm}on EQ & (436) & 354 & +59 & -4 & 370 & +36 & -21 \\
%\hspace{0.2cm}on PEQ & (181) & 38 & +7 & -4 & 51 & +9 & -4   \\

\hspace{0.1cm}with idempotency &  &  & +61 & -21  &  & +44 & -26\\&&&&&&\\

%\hspace{0.2cm}on EQ & (436) & 354 & +56 & -17 & 370 & +35 & -22\\
%\hspace{0.2cm}on PEQ & (181) & 38 & +5 & -4 & 51 & +9 & -4 \\&&&&&&\\

ordification  & (326) & 236 & +50 & -1 & 288 & +1 & -1\\&&&&&&\\

detransification  & (2007) & 1196 & +92 & -58 & 1387 & \bf{+73} & -31\\ 
%\hspace{0.2cm}on EQ& (436) & 354 & +53 & -8 & 370 & +31 & -8 \\
%\hspace{0.2cm}on PEQ& (181) &38&+17&-0&51&+16&-0\\
%\hspace{0.2cm}on TO& (326) &255&+0&-26&289&+1&-3\\
%\hspace{0.2cm}on R& (1359)&878&+69&-46&999&\bf{+44}&-24\\&&&&&&\\

\hspace{0.1cm}with reflexivity & (1359) & 870 & +66 & -135 & 999 & +40 & -110\\ 
%\hspace{0.3cm}on EQ& (436) & 354&+57&-22&370&+32&-45\\
%\hspace{0.3cm}on TO& (326 )& 255&+0&-71&289&+3&-8\\




%ordification  & (328) & & n/a & & 296 & {\bf +16} & \underline{-12} & 238 & {\bf +51} & \underline{-13} & 267 & {\bf +13} &  \underline{-15} & 0 & 0 & 0\\
%maxification  & (328) & 273 & +1 & -23 & 296 & +2 & -0 & 238 & +1 & -41 & 267 & +4 & \underline{-0} & 0 & 0 & 0\\
\end{tabular}
%\vspace{-0.5cm}
\caption{Table showing for each theorem prover the number of test problems solved before the transformation,  how many new problems are solved after the transformation, and the number of problems that could be solved before but not after the transformation. (Total number of applicable problems for each transformation in parentheses). A {\bf +value} in boldface indicates that there were hard problems (Rating 1.0) solved with that combination of treatment and theorem prover. 
%An underlined \underline{-value} indicates that time slicing (running both methods in 50\% of the time each) solves a strictly larger superset of problems with that combination of treatment and theorem prover. NOT TRUE ANYMORE
%- All except Trans_Ref for z3 solve problems with rating 1!
}
\label{fig:overview}
\end{figure}

Overall, the results vary between each transformation and reasoning tool. For many of the transformations, we don't gain any solved problems without also losing some. For Spass and CVC4, this was the case for all of the transformations. A time-slicing strategy can be advantageous, were the reasoning tool is run on both the original and the transformed problem, with a suitably chosen time-limit for each. 
Z3 turns out to work really well on ordified problems, where it can make use of its built in strategies for arithmetic. E did not benefit from any of the transformations, and a large portion of the problems became unsolvable. One may have expected better results for equalification, since introducing equality in place of each occurrence of an equivalence relation seems suitable for an equational theorem prover. However, E performs well already on the untreated problems with equivalence relations, leaving little room for improvement. Vampire has the least difference in performance before and after the transformations, demonstrating its stability as a theorem prover. 

In order to make a comparison between the transformations and evaluate what transformation works best for each kind of transitive relation, we partition the test problems into different subsets (Fig. 

\ref{fig:subsets}). These subsets are defined by the discovered properties of the transitive relation. A problem can appear in several subsets if the problem includes several transitive relations having different properties. This is the case for 156 problems. Apart from such special cases, the subsets are disjoint. Firstly, we divide the problems into two sets, one where the transitive relation is found to be total (or strictly total, as in the case of a negated total order), and one where this was not the case. We use the notation P\textsuperscript{C} to denote the subset of problems with transitive relations with no syntactic evidence of the property P.

The problems in Total\textsuperscript{C} are further divided into four groups, depending on if they have a transitive relation that is found to be reflexive and/or symmetric. The problems with total relations are partitioned into two sets: problems with one or more total order (i.e. total, transitive and antisymmetric), and problems with relations that are total and transitive but lack the antisymmetry property (labelled as "other" in the diagram). Fig. \ref{fig:subsets} shows each subset with its number of problems and number of rating 1 problems, and what transformation is applicable for each subset. For example, a problem with a transitive relation that is in Total\textsuperscript{C}, Reflexive\textsuperscript{C} and Symmetric has the applicable transformations Pequalification and Detransification, as shown in the bottom left corner of the diagram. The number of rating 1 problems in each subset can give an indication of the difficulty of dealing with different kinds of transitive relations. Problems with equivalence relations are solvable much more often than problems with partial equivalence relations, However it is hard to tell if the difficulty of a problem is related to the transitive relation or has other reasons. 

% \begingroup

\begin{figure}[h!]
\def\mca#1{\multicolumn{1}{c}{#1}}
\renewcommand{\arraystretch}{2.25}
\begin{center}
\begin{tabular}{r||p{16em}||p{16em}||}
  \mca{} & \multicolumn{2}{c}{Total\textsuperscript{C}} \\\cline{2-3}
%  \multirow{6}{*}{Reflexive}               & Equivalences & Partial orders  \\\cline{2-3}
   Reflexive               & \bf{Equivalences (436/2)} & \bf{Partial orders (540/135)}  \\ %\cline{2-3}
                 & Detransification & Detransification \\
                 & Detransification with reflexivity & Detransification with reflexivity \\
                 & Equalification & \\
                 & Pequalification &  \\
                 & Detransification & \\\cline{2-3} 
 % 
 {Reflexive\textsuperscript{C}} & \bf{Partial equivalences (181/74)} &  \bf{Strict Partial orders (607/124)}\\%\cline{2-3}
                                               & Pequalification  & Detransification\\
                                               & Detransification & \\\cline{2-3}
   \mca{} & \mca{Symmetric} & \mca{Symmetric\textsuperscript{C}}
\end{tabular}
\end{center}
\def\mca#1{\multicolumn{1}{c}{#1}}
\renewcommand{\arraystretch}{2.25}
\begin{center}
\begin{tabular}{r||p{16em}||}
  \mca{} & \multicolumn{1}{c}{Total/Strictly Total} \\\cline{2-2}
  Antisymmetric/Strictly Antisymmetric & \bf{(Strict) Total Orders (326/28)} \\%\cline{2-2}
                         & Ordification \\
                          & Detransification \\\cline{2-2} 
  Antisymmetric\textsuperscript{C} & \bf{Other (73/12)} \\%\cline{2-2}
                               & Detransification \\\cline{2-2} 
  \mca{} & \mca{} 
\label{fig:subsets}
\end{tabular}
\end{center}
%\endgroup
\label{fig:subsets}
\caption{Partitioning of test problems and their applicable transformations}
\end{figure}



\subsection{Detransification}
Detransification is the only transformation applicable on all 2007 test problems with transitive relations. As can be seen in Fig. \ref{fig:overview}, the benefits of detransification varies with the theorem prover and problem. The SMT-solvers profit the most from this transformation, however, big differences can be seen in the different subsets.  Fig. \ref{fig:transplots} presents an overview of the effects on solving times for each theorem prover in the evaluation. For all of the theorem provers, detransification lets us prove some problems that we could not previously, but some problems also become unsolvable within the time limit.

Fig. \ref{fig:detranssubsets} presents the results of detransification on each of the subsets defined in Fig. \ref{fig:subsets}. Here we can get an indication of what problems detransification is useful for and what kind of problems tend to become harder after the transformation. For E, the results generally become worse after detransification, even though some new problems become solvable, including a couple with rating 1. For Vampire, detransification improves the results on problems with partial orders and partial equivalence relations. These subsets have a relatively low success rate before the transformations.  On the other subsets, the results stay fairly stable. For Spass, partial equivalences and strict partial orders benefit the most from detransification, while the other subsets show mixed results. Both SMT-solvers, Z3 and CVC4, show improved results on the transformed equivalence relations and partial equivalence relations, which have in common that they are transitive and symmetric. The theorem provers performed well on these problems already before the transformation and thus have less room for improvement. For partial orders and strict partial orders, the results are mixed, however more is gained than what is lost. Total orders and other transitive relations do not benefit from detransification using any of the reasoning tools in our evaluation.

\begin{figure}[h!]
\def\mca#1{\multicolumn{1}{c}{#1}}
\renewcommand{\arraystretch}{2.25}
\begin{center}
\begin{tabular}{|| l l l l || l l l l ||}
                 \cline{1-8}
                 \multicolumn{4}{||l||}{\bf{Equivalences (436)}} & \multicolumn{4}{l||}{\bf{Partial Orders (540)}} \\
                 \cline{1-8}
                 E            & 427 & +4 & -24 & E  & 281 & +4 & -15  \\
                 Vampire & 434 & +0 & -0 & Vampire & 287 & \bf{+33} & -6  \\
                 Spass    & 385 & +15 & -32 &  Spass   & 201 & +15 & -15 \\
                 CVC4    & 370 & +31 & -8 &   CVC4  & 292 & \bf{+13} & -10 \\
                 Z3         & 354 & +53 & -8 &   Z3   & 215  & +18 & -10  \\
                 \cline{1-8} 
                 \multicolumn{4}{||l||}{\bf{Partial Equivalences (181)}} & \multicolumn{4}{l||}{\bf{Strict Partial Orders (607)}} \\
                 \cline{1-8}
                 E & 97 & \bf{+1} & -8 & E & 421 & \bf{+5}  & -31  \\
                 Vampire & 92 & +5 & -0 & Vampire & 444 & +5 & -11  \\
                 Spass & 67 & +8 & -0 & Spass & 299 & +48 & -9  \\
                 CVC4 & 51 & +16 & -0 & CVC4 & 341 & +29 & -7  \\
                 Z3 & 38 & +18 & -0 & Z3 & 290 & +24 & -12  \\\cline{1-8} 
\end{tabular}  \\

\begin{tabular}{|| l l l l || l l l l ||}
                 \cline{1-8}
                 \multicolumn{4}{||l||}{\bf{Total Orders (326)}}  &   \multicolumn{4}{||l||}{\bf{Other (73)}}  \\
                 \cline{1-8}
                  E           & 272 & +2 & -25 &  E & 57 & +0 & -7   \\
                 Vampire & 296 & +0 & -2 &  Vampire & 58 & +0 & -2    \\
                 Spass    & 243 & +9 & -34 &  Spass & 47 & +2 & -0   \\
                 CVC4    & 289 & +1 & -3 &   CVC4 & 55 & +2 & -3  \\
                 Z3         & 255 & +0 & -26 &    Z3 & 51 & +0 & -2    \\
                 \cline{1-8} 
\end{tabular}
\end{center}
\caption{The effect of detransification on each subset}
\label{fig:detranssubsets}
\end{figure}

\subsection{Detransification with reflexivity}
Detransification with reflexivity is applicable only on transitive relations that are reflexive. It shows worse results than detransification without reflexivity on all subsets for most provers. This is especially the case for the SMT-solvers, for which many problems become unsolvable. Only Vampire is slightly better with the reflexivity version, and solves in total 32 new problems (all with partial orders), while it loses none. The results on each applicable subset is shown in Fig. \ref{fig:detransreflsubsets}

\begin{figure}[h!]
\begin{tabular}{|| l l l l || l l l l ||}
                 \cline{1-8}
                 \multicolumn{4}{||l||}{\bf{Equivalences (436)}} & \multicolumn{4}{l||}{\bf{Partial Orders (540)}} \\
                 \cline{1-8}
                 E            & 427 & +3 & -30 & E  & 281 & +1 & -20  \\
                 Vampire & 434 & +0 & -0 & Vampire & 287 & \bf{+32} & -0  \\
                 Spass    & 385 & +14 & -44 &  Spass   & 201 & +8 & -16 \\
                 CVC4    & 370 & +32 & -45 &   CVC4  & 292 & +5 & -55 \\
                 Z3         & 354 & +57 & -22 &   Z3   & 215  & +12 & -41  \\
                 \cline{1-8} 
\end{tabular}

\begin{tabular}{|| l l l l || l l l l ||}
                 \cline{1-8}
                 \multicolumn{4}{||l||}{\bf{Total Orders (326)}}  &   \multicolumn{4}{||l||}{\bf{Other (73)}}  \\
                 \cline{1-8}
                  E           & 272 & +2 & -34 &  E & 57 & +0 & -7   \\
                 Vampire & 296 & +0 & -0 &  Vampire & 58 & +0 & -0    \\
                 Spass    & 243 & +5 & -31 &  Spass & 47 & +2 & -0   \\
                 CVC4    & 289 & +3 & -8 &   CVC4 & 55 & +2 & -4  \\
                 Z3         & 255 & +0 & -71 &    Z3 & 51 & +0 & -3    \\
                 \cline{1-8} 

\end{tabular}
\caption{The effect of detransification with reflexivity on each applicable subset}
\label{fig:detransreflsubsets}
\end{figure}

\subsection{Pequalification}
Pequalification is applicable on any relation that is transitive and symmetric, i.e. both equivalence relations and partial equivalence relations. The results on these subsets are presented in Fig. \ref{fig:peqsubsets}. SMT-solvers benefit the most from pequalification, especially Z3 on the set of problems with equivalence relations. Fig. \ref{figpeqsubsetsidem} shows the variant with the added idempotency axiom. All of the tested reasoning tools perform about the same or worse given this extra axiom.

Comparing pequalification with detransification, detransification is clearly much better for partial equivalence relations, while for equivalence relations it is not as clear which transformation one should pick. Pequalification without idempotency seems to be a good choice on equivalence relations for SMT-solvers, especially for Z3.

\begin{figure}[h!]
\begin{tabular}{|| l l l l || l l l l ||}
                 \cline{1-8}
                 \multicolumn{4}{||l||}{\bf{Equivalences (436)}}  &   \multicolumn{4}{||l||}{\bf{Partial Equivalences (181)}}  \\
                 \cline{1-8}
                  E           & 427 & +5 & -33 &  E & 97 & +0 & -36   \\
                 Vampire & 434 & +0 & -2 &  Vampire & 92 & +5 & -6    \\
                 Spass    & 385 & +16 & -46 &  Spass & 67 & +2 & -2   \\
                 CVC4    & 370 & +36 & -21 &   CVC4 & 51 & +9 & -4  \\
                 Z3         & 354 & +59 & -4 &    Z3 & 38 & +9 & -4    \\
                 \cline{1-8} 
\end{tabular} 
\label{fig:peqsubsets}
\caption{The effect of pequalification on each applicable subset}
\end{figure}

\begin{figure}[h!]
\begin{tabular}{|| l l l l || l l l l ||}
                 \cline{1-8}
                 \multicolumn{4}{||l||}{\bf{Equivalences (436)}}  &   \multicolumn{4}{||l||}{\bf{Partial Equivalences (181)}}  \\
                 \cline{1-8}
                  E           & 427 & +3 & -59 &  E & 97 & +0 & -36   \\
                 Vampire & 434 & +0 & -7 &  Vampire & 92 & +6 & -6    \\
                 Spass    & 385 & +14 & -40 &  Spass & 67 & +5 & -2   \\
                 CVC4    & 370 & +35 & -22 &   CVC4 & 51 & +9 & -4  \\
                 Z3         & 354 & +56 & -17 &    Z3 & 38 & +7 & -4    \\
                 \cline{1-8} 
\end{tabular} 
\label{fig:peqsubsetsidem}
\caption{The effect of pequalification with idempotency on each applicable subset}
\end{figure}

\subsection{Equalification}

results after adding the idempotency axiom follows the same pattern as for pequalification:
making the results slightly worse. the most significant change is for E.
equalification is slightly worse or about the same compared to pequalification.

\begin{figure}[h!]
\begin{tabular}{|| l l l l ||}
                 \cline{1-4}
                 \multicolumn{4}{||l||}{\bf{Equivalences (436)}}  \\
                 \cline{1-4}
                  E           & 427 & +5 & -38   \\
                 Vampire & 434 & +0 & -7    \\
                 Spass    & 385 & +16 & -46   \\
                 CVC4    & 370 & +35 & -20   \\
                 Z3         & 354 & +60 & -7   \\
                 \cline{1-4} 
\end{tabular} 
\label{fig:peqsubsetsidem}
\caption{The effect of equalification on the applicable subset}
\end{figure}

\begin{figure}[h!]
\begin{tabular}{|| l l l l ||}
                 \cline{1-4}
                 \multicolumn{4}{||l||}{\bf{Equivalences (436)}}  \\
                 \cline{1-4}
                  E           & 427 & +4 & -56   \\
                 Vampire & 434 & +0 & -6   \\
                 Spass    & 385 & +14 & -43   \\
                 CVC4    & 370 & +35 & -22   \\
                 Z3         & 354 & +59 & -11   \\
                 \cline{1-4} 
\end{tabular} 
\label{fig:peqsubsetsidem}
\caption{The effect of equalification with idempotency on the applicable subset}
\end{figure}

\subsection{Ordification}
Since ordification uses arithmetic, it is only applicable with Vampire (in TFF format) and Z3 and CVC4 (in SMT format). The original problems were transformed into TFF and SMT as well, in order to achieve a fair comparison. It is applicable only on the set of problems containing total orders. Ordification improved the results significantly for Z3, while CVC4 and Vampire perform about the same as before the transformation.

\begin{figure}[h!]
\begin{tabular}{|| l l l l ||}
                 \cline{1-4}
                 \multicolumn{4}{||l||}{\bf{Total Orders (326)}}  \\
                 \cline{1-4}
                 Vampire & 295 & +1 & -0   \\
                 CVC4    & 370 & +1 & -1   \\
                 Z3         & 354 & +50 & -1   \\
                 \cline{1-4} 
\end{tabular} 
\label{fig:ordsubset}
\caption{The effect of ordification on the applicable subset}
\end{figure}



We can compare ordification with detransification, which is the only other transformation that is applicable on total orders. Similarly to ordification, detransification does not have any significant impact on the results for either of CVC4 or Vampire on total orders. For Z3, ordification is clearly the best choice. Note however that Z3 shows worse results than CVC4 and Vampire prior to the transformation. After ordification, the three tools solve about the same number of problems.

\subsection{Problems with more than one kind of transitive relation}
156 of the problems in our evaluation contain more than one kind of transitive relation. 140 of them contain a partial equivalence relation and a strict partial order. 14 contain an equivalence relation and a partial order, and two problems contain a partial equivalence relation and a relation that is total and transitive. Almost 50\% of these problems are hard, with rating 1 in the TPTP.

For the 140 problems with a partial equivalence and a strict partial order, we found that applying detransification on all of the transitive relations gave the best results. 
For the 14 problems with equivalence relation and a partial order, applying equalification on the equivalence relation and detransification on the partial order was the best, in particular for the SMT-solvers. 
The 2 remaining problems with multiple kinds of transitive relations are both labelled as Unknown, and were not solved before nor after any choice of transformation.

\subsection{"Recipes"}




\section{Discussion and Conclusions}

We have presented 6 transformations that can be applied to theories with certain transitive relations: equalification, pequalification, ordification, maxification, detransification, and detransification with reflexivity. We have also created a method for syntactic discovery of binary relations where these transformations are applicable.

For users of reasoning tools that create their own theories, it is clear that they should consider using one of the proposed alternative treatments when writing theories. For all of our methods, there are existing theories for which some provers performed better on these theories than others. In particular, there exist 18 TPTP problems that are now solvable that weren't previously.

For implementers of reasoning tools, our conclusions are less clear. For some combinations of treatments and provers (such as transification for Vampire, and equalification for Z3), overall results are clearly better, and we would thus recommend these treatments as preprocessors for these provers. Some more combinations of treatments and provers lend themselves to a time slicing strategy that can solve strictly more problems, and could thusly be integrated in a natural way in provers that already have the time slicing machinery in place.

\section{Future Work}

There are many other relations that are more or less common that could benefit from an alternative treatment like the transformations described in this paper. In particular, maxification seems to be an idea that could be applied to binary relations that are weaker than total orders, which may make this treatment more effective. But there are also other, non-transitive relations that are of interest.

There are other kinds of relations than binary relations. For example, we can have an ternary relation that behaves as an equivalence relation in its 2nd and 3rd argument. An alternative treatment of this relation would be to introduce a binary function symbol |rep_|. We do not know whether or not this occurs often, and if it is a good idea to treat higher-arity relational symbols specially in this way.

Lastly, we would like to look at how these ideas could be used inside a theorem prover; as soon as the prover discovers that a relation is an equivalence relation or a total order, one of our transformations could be applied, on the fly. The details of how to do this remain to be investigated.

\section*{Acknowledgments}

We thank Nicholas Smallbone for discussions and useful suggestions on earlier versions of this paper.

\appendix

\begin{figure}[t!]
\includegraphics[scale=0.65,trim=10mm 00mm 20mm 0mm]{Plots/Transified/E/test_original_e_transified_e_300.eps}
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/Transified/Vampire/test_original_vampire_transified_vampire_300.eps}\\
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/Transified/Spass/test_original_spass_transified_spass_300.eps} 
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/Transified/Z3/test_original_z3_transified_z3_300.eps} \\
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/Transified/CVC4/test_original_cvc4_transified_cvc4_300.eps}
\caption{Effects of transification, using E, Vampire, Spass, Z3 and CVC4 }
%\includegraphics[scale=0.22]{Plots/Equalified/E/}
%\end{figure}
\label{fig:transplots}
\end{figure}

\begin{figure}[h!]
\includegraphics[scale=0.65,trim=10mm 00mm 20mm 0mm]{Plots/Equalified/E/test_original_e_equalified_e_300.eps}
%\includegraphics[scale=0.22]{Plots/Equalified/E/}
%\begin{figure}[t]
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/Equalified/Vampire/test_original_vampire_equalified_vampire_300.eps}\\
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/Equalified/Z3/test_original_z3_equalified_z3_300.eps}
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/Equalified/CVC4/test_original_cvc4_equalified_cvc4_300.eps}\\
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/Equalified/Spass/test_original_spass_equalified_spass_300.eps}
\caption{The time taken to solve problems, with and without equalification, using E, Vampire, Z3 and CVC4 }
%\includegraphics[scale=0.22]{Plots/Equalified/E/}
%\end{figure}
\label{fig:e_equalified}
\end{figure}


% ------------------------------------------------------------------------------
% - references

\bibliographystyle{plain}
\bibliography{main}

\end{document}

