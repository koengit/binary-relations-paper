\documentclass[smallcondensed,final]{svjour3}
%\usepackage{onecolceurws} % removed by Koen because it interacts with svjour3
%\usepackage{subcaption} % removed by Koen because svjour3 complained
\usepackage{anyfontsize} % added by Koen because some font sizes were not available
\usepackage{amssymb}
\usepackage{mathabx}
\usepackage{graphicx}
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

\begin{figure}[t]
\setlength{\tabcolsep}{5.2pt}
\begin{tabular}{lr||rrr||rrr||rrr}
  & & \multicolumn{3}{c||}{E} & \multicolumn{3}{c||}{Vampire} & \multicolumn{3}{c}{Spass} \\
\hline 
&&&&&&&&&&\\
equalification & (477) & 434 & +39  & \underline{-38} & 451 & +24  & -7 & 388 & +54 & \underline{-46}\\
\hspace{0.1cm}with idempotency &   &   &  +38  & \underline{-56} &  & +24  & -6 &   & +52 & \underline{-43}\\
pequalification & (656) & 531 & +39 & -69 & 543 &  +29 & -8 & 455 & +56 & \underline{-48}\\
\hspace{0.1cm}with idempotency &  &  &  +37  & -95  &  &  +30 & -13 & & +54 & \underline{-45}\\
detransification  & (2048) & 1490 & +49 & -101 & 1559 &  +62 & -21 & 1203 & +126 & -90\\
\hspace{0.1cm}with reflexivity & (1400) & 1032 & +40 & -89 & 1079 &  +56 & -20 &869 & +67 & -90\\
ordification & (326) & 272 & n/a & n/a & 295 &  +0& -1 & 243 & n/a & n/a\\
%ordification  & (328) & & n/a & & 296 & {\bf +16} & \underline{-12} & 238 & {\bf +51} & \underline{-13} & 267 & {\bf +13} &  \underline{-15} & 0 & 0 & 0\\
%maxification  & (328) & 273 & +1 & -23 & 296 & +2 & -0 & 238 & +1 & -41 & 267 & +4 & \underline{-0} & 0 & 0 & 0\\
\end{tabular}
%\end{center}
%\vspace{-0.5cm}
\label{fig:overview}
\end{figure}
\begin{figure}[t]
\setlength{\tabcolsep}{5.2pt}
\begin{tabular}{lr||rrr||rrr}
  & & \multicolumn{3}{c||}{Z3} &\multicolumn{3}{c}{CVC4}  \\
\hline 
&&&&&&&\\
equalification & (477) & 362 & +88 & \underline{-7} & 382 & +64 & -20\\
\hspace{0.1cm}with idempotency &   &   & +86  & -11 &  & +64 & \underline{-22}\\
pequalification & (656) & 400 &  +88  & -8  & 433 & +74 & -25\\
\hspace{0.1cm}with idempotency &  & & +83 & \underline{-21}  &  & +73 & -26\\
detransification  & (2048) & 1196 & +114 & -58 & 1387 & +102 & -31\\
\hspace{0.1cm}with reflexivity & (1400) & 878 & +66 & -135 & 1011 & +43 & -110\\
ordification  & (326) & 236 & +50 & -1 & 288 & +1 & -1\\
%ordification  & (328) & & n/a & & 296 & {\bf +16} & \underline{-12} & 238 & {\bf +51} & \underline{-13} & 267 & {\bf +13} &  \underline{-15} & 0 & 0 & 0\\
%maxification  & (328) & 273 & +1 & -23 & 296 & +2 & -0 & 238 & +1 & -41 & 267 & +4 & \underline{-0} & 0 & 0 & 0\\
\end{tabular}
%\vspace{-0.5cm}
\caption{Table showing for each theorem prover the number of test problems solved before the transformation,  how many new problems are solved after the transformation, and the number of problems that could be solved before but not after the transformation. (Total number of applicable problems for each transformation in parentheses). A {\bf +value} in boldface indicates that there were hard problems (Rating 1.0) solved with that combination of treatment and theorem prover. An underlined \underline{-value} indicates that time slicing (running both methods in 50\% of the time each) solves a strictly larger superset of problems with that combination of treatment and theorem prover.
%- All except Trans_Ref for z3 solve problems with rating 1!
}
\label{fig:overview}
\end{figure}


%KOEN: what tptp version did you use to generate the lagom stora problems?

\section{Experimental results}
We evaluate the effects of the different axiomatizations using three different resolution based theorem provers, E 2.0 \cite{E} (with the \textit{xAuto} and \textit{tAuto} options), Vampire 4.0 \cite{Vampire} (with the \textit{casc mode} option), Spass 3.9 \cite{spass}  and two SMT-solvers, Z3 4.5 \cite{Z3} and CVC4 1.5 \cite{CVC4}. The experiments were performed on a 2xQuad Core Intel Xeon E5620 processor with 24 GB physical memory, running at 2.4 GHz. We use a time limit of 5 minutes on each problem.
%NOT TRUE ANYMORE:
%For Vampire, no time limit is passed directly to the theorem prover but instead the process is terminated once the time limit has passed. This was done to keep solving times more stable, since Vampire uses %the time limit to control its search strategies.

We started from a set of 13410 test problems from the TPTP, listed as Unsatisfiable, Theorem, Unknown or Open (leaving out the very large theories). For each problem, a new theory was generated for each applicable transformation. For most problems, no relation matching any of the given criteria was detected, and thus no new theories were produced for these problems. Evaluation of reasoning tools on Satisfiable and CounterSatisfiable problems is left as future work.

The experimental results are summarized in Fig.\ \ref{fig:overview}.

\begin{figure}[t]
\begin{center}
\includegraphics[scale=0.65,trim=10mm 00mm 20mm 0mm]{Plots/Equalified/E/test_original_e_equalified_e_300.eps}
%\includegraphics[scale=0.22]{Plots/Equalified/E/}
%\begin{figure}[t]
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/Equalified/Vampire/test_original_vampire_equalified_vampire_300.eps}\\
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/Equalified/Z3/test_original_z3_equalified_z3_300.eps}
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/Equalified/CVC4/test_original_cvc4_equalified_cvc4_300.eps}
\end{center}
\caption{The time taken to solve problems, with and without equalification, using E, Vampire, Z3 and CVC4 }
%\includegraphics[scale=0.22]{Plots/Equalified/E/}
%\end{figure}
\label{fig:e_equalified}
\end{figure}

\subsection{Equivalence relations}

Equivalence relations were present in 477 of the test problems. The majority of these problems appear in the GEO and SYN categories. Interestingly, among these 477 problems, there are only 29 problems whose equivalence relations are axiomatized with transitivity axioms. The remaining problems axiomatize equivalence relations with euclidean and reflexivity axioms, as discussed in section \ref{sec:discovery}. The number of equivalence relations in each problem ranges from 1 to 40, where problems with many equivalence relations all come from the SYN category. There is no clear correspondence between the number of equivalence relations in a problem and the performance of the prover prior to and after the transformation. 

\paragraph{Equalification}
As can be seen in Fig. \ref{fig:overview}, equalification performs very well with Z3, and somewhat well with CVC4, while it worsens the results of the resolution based provers, which already performed well on the original problems. %TODO : Koen - why may this be? 
Using a time slicing strategy, which runs the prover on the original problem for half the time and on the transformed problem for the second half, solves a strict superset of problems than the original for all of the theorem provers used in the evaluation. Fig. \ref{fig:e_equalified} shows in more detail the effect on solving times for the different theorem provers.
%TODO: for the camera ready version we should make the time slicing squares the biggest possible size.

%TODO KOEN: i don't like the word treatment. it sounds like a cream you put on your skin.

\paragraph{Pequalification}
In 181 of the test problems, relations that are transitive and symmetric, but not reflexive, were found. The majority of these problems are in the CAT and FLD categories of TPTP. All of the tested theorem provers perform worse on these problems compared to the problems with true equivalence relations. This is also the case after performing pequalification. Pequalification turns out to be particularly bad for E, which solves 34 fewer problems after the transformation. Pequalification makes Z3 perform only slightly better and Vampire and CVC4 slightly worse.
%When the differences to the performance is small, it is hard to know if the effect is due to the new axiomatisation, or to other reasons.
%For example, we have observed that simply shuffling the axioms of a theory can cause the results to deviate in a similar way. 
%TODO Koen can we say anything more here?

\paragraph{Hard problems solved using Pequalification}
After Pequalification, one problem with rating 1.0 (FLD041-2) is solved by Vampire. Rating 1.0 means that no known current theorem prover solves the problem in reasonable time.

\subsection{Total orders}
Total orders were found in 328 problems. The majority are in the SWV category, and the remaining in HWV, LDA and NUM.  In 77 of the problems, the total order is positively axiomatized, and in the other 251 problems it is negative (and thus axiomatized as a strict total order). There is never more than one order present in any of the problems. 

\begin{figure}[t]
%\includegraphics[scale=0.40,trim=20mm 00mm 30mm 0mm]{Plots/Ordified/E/test_original_e_ordified_e_300.eps}
%\includegraphics[scale=0.22]{Plots/Equalified/E/}
%\begin{figure}[t]
\begin{center}
%\includegraphics[scale=0.55,trim=20mm 0mm 30mm 0mm]{Plots/Ordified/Vampire/test_original_vampire_ordified_vampire_300.eps}
\includegraphics[scale=0.55,trim=7mm 0mm 30mm 0mm]{Plots/Ordified/Z3/test_original_Z3_ordified_Z3_300.eps}
\includegraphics[scale=0.55,trim=7mm 0mm 40mm 0mm]{Plots/Ordified/CVC4/test_original_CVC4_ordified_cvc4_300.eps}
\end{center}
%\includegraphics[scale=0.22]{Plots/Equalified/E/}
\caption{Effects of ordification, using Vampire, Z3 and CVC4 }
\label{fig:ordified}
\end{figure}

\paragraph{Ordification}
For each of the problems, we ran the theorem provers with built-in support for arithmetic on the problems before and after applying ordification. Vampire was run on a version in TFF format \cite{TFF}, and Z3 and CVC4 on a version in SMT format \cite{SMT-LIB}. The original problems were also transformed into TFF and SMT in order to achieve a relevant comparison. Ordification performs well for Z3, while for Vampire and CVC4 it is good for some problems and bad for some.
Fig.\ \ref{fig:ordified} shows how solving times are affected, and the diagrams also show great potential for time slicing, in particular for Vampire and Z3.

\paragraph{Hard problems solved using Ordification}
After Ordification, 15 problems, all from the SWV category, with rating 1.0 are solved. (SWV004-1, SWV035+1, SWV040+1, SWV044+1, SWV049+1, SWV079+1, SWV100+1, SWV101+1, SWV108+1, SWV110+1, SWV113+1, SWV118+1, SWV120+1, SWV124+1, SWV130+1) Vampire and Z3 each solve 14 hard problems and CVC4 solves 13 of them. One problem (SWV004-1) is even categorized as Unknown, which means that no prover has ever solved it. After ordification, all three provers were able to solve it in less than a second.

\paragraph{Maxification}
Maxification, our second possible treatment of total orders, turned out to be disadvantageous to E and Z3, while having a small positive effect on Vampire and CVC4 (see Fig.\ \ref{fig:overview}).
%TODO Koen what may be a reason for this?

%\begin{figure}[t]
%\includegraphics[scale=0.70,trim=10mm 00mm 20mm 0mm]{Plots/Maxified/E/test_original_e_maxified_e_300.eps}
%\includegraphics[scale=0.22]{Plots/Equalified/E/}
%\begin{figure}[t]
%\includegraphics[scale=0.70,trim=10mm 0mm 20mm 0mm]{Plots/Maxified/Vampire/test_original_vampire_maxified_vampire_300.eps}\\
%\includegraphics[scale=0.70,trim=10mm 0mm 20mm 0mm]{Plots/Maxified/Z3/test_original_z3_maxified_z3_300.eps} 
%\includegraphics[scale=0.70,trim=10mm 0mm 20mm 0mm]{Plots/Maxified/CVC4/test_original_cvc4_maxified_cvc4_300.eps}
%\caption{Effects of maxification, using E, Vampire, Z3 and CVC4 }
%\includegraphics[scale=0.22]{Plots/Equalified/E/}
%\end{figure}
%\end{figure}


\subsection{Transitive and Reflexive relations}
573 test problems include relations that are transitive and reflexive, excluding equivalence relations and total orders. In all of them, transitivity occurs syntactically as an axiom. The problems come from a variety of categories, but a vast majority are in SET, SEU and SWV.  Only about half of the original problems were solved by each theorem prover, which may indicate that transitivity axioms are difficult for current theorem provers to deal with.  We evaluate the performance of the theorem provers before and after transification. Problems that include equivalence relations and total orders are excluded, as the corresponding methods equalification and ordification give better results and should be preferred. Vampire benefits the most from transification, and solves 32 new problems after the transformation, while 10 previously solvable problems become unsolvable within the time limit. For E, the effect of transification is almost exclusively negative.
%TODO what to write here?? 
Vampire also has a significantly worse performance than E overall on the original problems that include relations that are transitive and reflexive.
Both Z3 and CVC4 perform worse after the transformation, but time slicing can be a good way to improve the results. 

%TODO KOEN: who uses chaining? is Vampire better on transified problems because it doesn't use chaining?

\begin{figure}[t]
\begin{center}
\includegraphics[scale=0.65,trim=10mm 00mm 20mm 0mm]{Plots/OnlyTransify/E/test_original_e_transified_e_300.eps}
%\includegraphics[scale=0.22]{Plots/Equalified/E/}
%\begin{figure}[t]
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/Transified/Vampire/test_original_vampire_transified_vampire_300.eps}\\
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/Transified/Z3/test_original_z3_transified_z3_300.eps} 
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/Transified/CVC4/test_original_cvc4_transified_cvc4_300.eps}
\end{center}
\caption{Effects of transification, using E, Vampire, Z3 and CVC4 }
%\includegraphics[scale=0.22]{Plots/Equalified/E/}
%\end{figure}
\end{figure}


\paragraph{Hard problems solved using Transification}
After transification, two new problems with rating 1.0 are solved, both by Vampire (SEU322+2 and SEU372+2).

\paragraph{Equalification and Transification}
Since all equivalence relations are transitive and reflexive, the method for transification works also on equivalence relations. Comparing the two methods on the 430 problems with equivalence relations, we concluded that equalification and transification work equally bad for E, Vampire and CVC4. Both transification and equalification improve the results for Z3, but equalification does so significantly. 

\paragraph{Ordification and Transification}
We compared ordification and transification on the 328 problems containing total orders. Transification seems to make these problems generally more difficult for theorem provers to solve, while ordification instead improved the results on many of the problems.  Transification makes the theorem prover perform worse on these problems also for E, which cannot make use of ordification since it does not provide support for arithmetic.

%(equalification: win 50 lose 3, transification: win 46, lose 27)

% ------------------------------------------------------------------------------
% - discussion and related work
% - conclusions and future work

\section{Discussion and Conclusions}

We have presented 6 transformations that can be applied to theories with certain transitive relations: equalification, pequalification, ordification, maxification, detransification, and detransification with reflexivity. We have also created a method for syntactic discovery of binary relations where these transformations are applicable.

For users of reasoning tools that create their own theories, it is clear that they should consider using one of the proposed alternative treatments when writing theories. For all of our methods, there are existing theories for which some provers performed better on these theories than others. In particular, there exist 18 TPTP problems that are now solvable that weren't previously.

For implementers of reasoning tools, our conclusions are less clear. For some combinations of treatments and provers (such as transification for Vampire, and equalification for Z3), overall results are clearly better, and we would thus recommend these treatments as preprocessors for these provers. Some more combinations of treatments and provers lend themselves to a time slicing strategy that can solve strictly more problems, and could thusly be integrated in a natural way in provers that already have the time slicing machinery in place.

\section{Future Work}

There are many other relations that are more or less common that could benefit from an alternative treatment like the transformations described in this paper. In particular, maxification seems to be an idea that could be applied to binary relations that are weaker than total orders, which may make this treatment more effective. But there are also other, non-transitive relations that are of interest.

There are other kinds of relations than binary relations. For example, we can have an ternary relation that behaves as an equivalence relation in its 2nd and 3rd argument. An alternative treatment of this relation would be to introduce a binary function symbol |rep_|. We do not know whether or not this occurs often, and if it is a good idea to treat higher-arity relational symbols specially in this way.

Lastly, we would like to look at how these ideas could be used inside a theorem prover; as soon as the prover discovers that a relation is an equivalence relation or a total order, one of our transformations could be applied, on the fly. The details of how to do this remain to be investigated.

% ------------------------------------------------------------------------------
% - references

\bibliographystyle{plain}
\bibliography{main}

\end{document}

