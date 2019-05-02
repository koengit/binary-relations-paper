\documentclass[smallcondensed,final]{svjour3}
%\usepackage{onecolceurws} % removed by Koen because it interacts with svjour3
%\usepackage{subcaption} % removed by Koen because svjour3 complained
\usepackage{anyfontsize} % added by Koen because some font sizes were not available
\usepackage{amssymb}
\usepackage{mathabx}
\usepackage{graphicx}
\usepackage{multirow}
%include polycode.fmt

%\def\comment#1{$\Rightarrow$ {\em #1} $\Leftarrow$}

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

%format §§      = "\hspace{-0.05cm}"

%format P  = "P\hspace{-0.1cm}"
%format P_ = "P"

%format m  = "m\hspace{-0.1cm}"
%format m_ = "m"

%format m1  = m'"\hspace{-0.1cm}"
%format m1_ = m'

%format R   = "R\hspace{-0.1cm}"
%format pR  = "+\hspace{-0.1cm}"R
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

%format propp = prop"\hspace{-0.1cm}"
%format prop1 = prop"_1"
%format propa = prop"_a"
%format propb = prop"_b"
%format propn = prop"_n"

%format a0 = a"_0"
%format a1 = a"_1"
%format a2 = a"_2"
%format ai = a"_i"
%format an = a"_n"

%format endproof = "\Box"

%format != = "\models "

% ------------------------------------------------------------------------------
% - abstract

\begin{abstract}
We present a number of alternative ways of handling transitive binary relations that commonly occur in first-order problems, in particular {\em equivalence relations}, {\em total orders}, and {\em transitive relations} in general. We show how such relations can be discovered syntactically in an input theory, and how they can be expressed in alternative ways. We experimentally evaluate different such ways on problems from the TPTP, using resolution-based reasoning tools as well as instance-based tools. Our conclusions are that (1) it is beneficial to consider different treatments of binary relations as a user, and that (2) reasoning tools could benefit from using a preprocessor or even built-in support for certain types of binary relations.
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
can lead to an expensive proof exploration in resolution and superposition based theorem provers, and can generate a huge number of instances in instance-based provers and SMT-solvers. Transitive relations are also common enough to motivate special built-in support. However, as far as we know, out of all the major first-order reasoning tools, chaining has only been implemented in SPASS \cite{spass}.

As an alternative to adding built-in support, in this paper we mainly look at (1) what a user of a reasoning tool may do herself to optimize the handling of these relations, and (2) how a preprocessing tool may be able to do this automatically.

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

For the purpose of this paper, we have decided to focus on three different kinds of transitive relations: (1) {\em equivalence relations} and {\em partial equivalence relations}, (2) {\em total orders} and {\em strict total orders}, and (3) general {\em transitive relations} and {\em reflexive, transitive relations}. The reason we decided to concentrate on these three are because (a) they appear frequently in practice, and (b) we found ways of dealing with these that worked well in practice.

The target audience for this paper is thus both people who use reasoning tools and people who implement reasoning tools.

\paragraph{Related Work} Chaining \cite{chaining} is a family of methods that limit the use of transitivity-like axioms in proofs by only allowing certain chains of them to occur in proofs. The result is a complete proof system that avoids the derivation of unnecessary consequences of transitivity. However, chaining has only been implemented in one of the reasoning tools we considered for this paper (SPASS). Also more specific binary relations that the ones considered in this paper have been implemented in this way \cite{simpl}. In personal communication with some of the authors of the other tools, chaining-like techniques have not been deemed important enough to be considered for implementation, and their preliminary experimental results were mostly negative.

Efficient reasoning procedures for binary relations have been introduced that are complete for finite models (e.g. \cite{decbinrel,relsmt}). This paper is concerned with reasoning about (transitive) binary relations in a general first-order setting.

% ------------------------------------------------------------------------------
% - properties of binary relations

\section{Common properties of binary relations} \label{sec:properties}

In this section, we take a look at commonly occurring properties of binary relations, which combinations of these are interesting for us to treat specially, and how we may go about discovering these. Note that the logic that we use throughout the paper is unsorted first-order logic with equality.

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

Take a look at Fig.\ \ref{fig:props}. It lists 8 basic and common properties of binary relations. Each of these properties can be expressed using one logic clause, which makes it easy to syntactically identify the presence of such a property in a given theory\footnote{Throughout the paper, we use the word theory to simply mean ``set of formulas''.}.

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
\vspace{-0.2cm}
\caption{Number of occurrences of binary relation properties in TPTP}
\label{fig:occurs}
\end{figure}

When we investigated the number of occurrences of these basic properties in a subset of the TPTP problem library (v7.0.0)\footnote{For the statistics in this paper, we decided to only look at unsorted TPTP problems with 10.000 clauses or less.} \cite{tptp}, we ended up with the table in Fig.\ \ref{fig:occurs}. The table was constructed by gathering all clauses from all TPTP problems (after clausification), and keeping every clause that only contained one binary relation symbol, no function symbols, and, possibly, equality. Each such clause was then syntactically categorized as an expression of a basic property of a binary relation symbol. The total number of such clauses found is indicated in the table for each basic property. We found 163 clauses that did not fit any of the 8 properties we chose as basic properties, but were instead instances of two new properties. Both of these were quite esoteric and did not seem to have a standard name in mathematics.

The table also contains occurrences where a {\em negated relation} was stated to have a certain property, and also occurrences where a {\em flipped relation} (a relation with its arguments swapped) was stated to have a certain property, and also occurrences of combined negated and flipped relations. This explains for example why the number of occurrences of {\em total} relations is the same as for {\em asymmetric} relations; if a relation is total, the negated relation is asymmetric and vice-versa.

We adopt the following notation. Given a relation |R_|, the {\em negated version} of |R_|, denoted |R_^~|, is defined as follows:
\begin{code}
forall x,y . R_^~(x,y) <=> ~R(x,y)
\end{code}
The  {\em flipped version} of |R_|, denoted |R_^^|, is defined as follows:
\begin{code}
forall x,y . R_^^(x,y) <=> R(y,x)
\end{code}
We lift these two notions to properties of relations as follows. Given a property of binary relations |prop|, we introduce its {\em negated version}, which is denoted by |prop^~|. The property |prop^~| holds for |R_| if and only if |prop| holds for |R_^~|:
\begin{code}
prop^~[R_] <=> propp[R_^~]
\end{code}
Similarly, we introduce the {\em flipped version} of a property |prop|, which is denoted by |prop^^|. The property |prop^^| holds for |R_| if and only if |prop| holds for |R_^^|:
\begin{code}
prop^^[R_] <=> propp[R_^^]
\end{code}
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
As a side note, in mathematics, strict total orders are sometimes defined using a property called {\em trichotomous}, which means that exactly one of |R(x,y)|, |x=y|, or |R(y,x)| must be true. However, when this property is clausified in the presence of transitivity, one ends up with |antisymmetric^~| which says that at least one of |R(x,y)|, |x=y|, or |R(y,x)| must be true. There seems to be no standard name in mathematics for the property |antisymmetric^~|, which is why we use this name.

\begin{figure}[t]
\begin{center}
\begin{tabular}{rrl}
500 & +48 & equivalence relations \\
154 & +2 & partial equivalence relations \\
250 & +4 & (strict) total orders \\
806 & +15 & reflexive, transitive relations (excluding the above) \\
1128& +69 & transitive relations (excluding the above) \\
\end{tabular}
\end{center}
\vspace{-0.3cm}
\caption{Number of occurrences of binary relations in TPTP, divided up into Theorem/Unsatisfiable/Unknown/Open problems +Satisfiable/CounterSatisfiable problems. }
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

To detect a binary relation |R_| with certain properties in a given theory, we simply gather all basic properties about |R_| that occur in the theory, and then compute which other properties they imply, using the pre-generated table.

Also, certain properties can be derived for a binary relation |R2_| if |R2_| is implied by another binary relation |R1_|, and |R1_| has that property. This holds for reflexivity, totality and seriality. Similarly, if |R2_| is antisymmetric or coreflexive, the same property can be derived for |R1_|. When having derived a new property of a relation in this way, we iterate the procedure of finding implied properties using the precomputed table until no new information is gained.  In this way, we never perform full theorem proving, but we nonetheless detect many binary relations with the listed basic properties. 

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

The transformation is correct, meaning that it preserves (non-)satisfiability:

\begin{theorem}[Correctness of equalification] Two theories |H| and |H'| that respectively match the LHS and RHS of equalification, are equisatisfiable. 
\end{theorem}
\begin{proof}
($\Rightarrow$) Assume we have |m_ != H|, then |m(R_)|\footnote{We write |m(R_)| for the interpretation of symbol |R_| in the model |m_|.} is an equivalence relation. Let the interpretation |m1_| interpret all existing symbols as |m_| does. Moreover, let |m1(rep_)| be a representative function of the equivalence relation |m(R_)|. This means that we have |m1_ != ( R(x,y) <=> rep(x)=rep(y) )|, which means that |m1_| is a model of |H'|.

($\Leftarrow$) Assume we have |m1_ != H'|. Let the interpretation |m_| interpret all existing symbols as |m1_| does. Moreover, let |m(R_) §§(x,y)| be interpreted by |m1(rep_)§§(x)=m1(rep_)§§(y)|. The relation |m(R_)| is clearly reflexive, symmetric, and transitive, and therefore we have |m_ != H|. |endproof|
\end{proof}

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

The transformation is correct, meaning that it preserves (non-)satisfiability:

\begin{theorem}[Correctness of pequalification] Two theories |H| and |H'| that respectively match the LHS and RHS of pequalification, are equisatisfiable. 
\end{theorem}
\begin{proof}
($\Rightarrow$) Assume we have |m_ != H|, then |m(R_)| is a partial equivalence relation. Let the interpretation |m1_| interpret all existing symbols as |m_| does. Moreover, let |m1(P_)| |m1(rep_)| be a representative function of the equivalence relation |m(R_)|. This means that we have |m1_ != ( R(x,y) <=> rep(x)=rep(y) )|, which means that |m1_| is a model of |H'|.

($\Leftarrow$) Assume we have |m1_ != H'|. Let the interpretation |m_| interpret all existing symbols as |m1_| does. Moreover, let |m(R_) §§(x,y)| be interpreted by |m1(rep_)§§(x)=m1(rep_)§§(y)|. The relation |m(R_)| is clearly reflexive, symmetric, and transitive, and therefore we have |m_ != H|. |endproof|
\end{proof}

Intuitively, one can see that this transformation is correct by realising that the elements on which the relation |R_| is not reflexive cannot be related to any other elements. This is because |R(x,y)| together with symmetry and transitivity gives us |R(x,x)|. Thus, when we encounter |R(x,y)| in the LHS theory, we know that both |x| and |y| are in the set defined by |P_|. (This holds also when |x| equals |y|). Since |R_| is an equivalence relation on this set, we can use the transformation of pure equivalence relations on the subset |P_| to get |P(x) && P(y) => rep(x) = rep(y)|.

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

The above transformation is correct, meaning that it preserves (non-)satisfiability:

\begin{theorem}[Correctness of ordification] Two theories |H| and |H'| that respectively match the LHS and RHS of ordification, are equisatisfiable. 
\end{theorem}
\begin{proof}
($\Rightarrow$) If we have |m_ != H|, then without loss of generality (by L{\"o}wenheim-Skolem), we can assume that the domain of |m_| is countable. Also, |m(R_)| is a total order. Let the interpretation |m1_| interpret all existing symbols as |m_| does. We now construct |m1(rep_)| recursively as a mapping from the model domain to |RR|, such that we have |m(R_)§§(x,y) <=> m1(rep_)(x)<=m1(rep_)(y)|, in the following way. Let |{a0, a1, a2, ..}| be the domain of the model, and set |m1(rep_)(a0):=0|. For any |n>0|, pick a value for |m1(rep_)(an)| that is consistent with the total order |R_| and all earlier domain elements |ai|, for |0 <= i < n|. This can always be done because there is always extra room for a new, unique element between any two distinct values of |RR|. Thus |m1(rep_)| is injective and we also have a model |m1_| of |H'|.

($\Leftarrow$) Assume we have |m1_ != H'|. Let the interpretation |m_| interpret all existing symbols as |m1_| does. Moreover, let |m(R_)§§(x,y):=m1(rep_)(x)<=m1(rep_)(y)|. It is clear that |m(R_)| is total and transitive, and also antisymmetric because |m1(rep_)| is injective, and therefore |m_ != H|. |endproof|
\end{proof}

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

The above transformation is correct, meaning that it preserves (non-)satisfiability: ($\Rightarrow$) If we have a model of the LHS theory, then |R_| must be interpreted as a total order. Let |max_| be the maximum function associated with this order. Clearly, it must be associative and commutative, and the third axiom also holds. Moreover, we have  |R(x,y) <=> max(x,y)=y|. Thus we also have a model of the RHS theory. ($\Leftarrow$) If we have a model of the RHS theory, let |R(x,y):=max(x,y)=y|. Given the axioms in the RHS theory, |R_| is total, antisymmetric, and transitive, and therefore we have a model of the LHS theory.

% ------------------------------------------------------------------------------
% - detransification

\section{Handling transitive relations in general}

The treatments introduced so far all make use of built-in concepts of the reasoning tool, and they can be applied only to special cases of transitive relations. In this section we propose a more general approach, in which theories with a transitivity axiom are transformed into theories without that transitivity axiom. To this end, transitivity is specialized at each {\em positive occurrence} of the relational symbol. Such transformations may be beneficial because reasoning about transitivity in a naive way can be very expensive for theorem provers, because from transitivity there are many possible conclusions to draw that trigger each other ``recursively''.

The transformations presented in this subsection only work on problems where every occurrence of |R_| is either positive or negative (and not both, such as under an equivalence operator). If this is not the case, the problem has to be translated into one where this is the case. This can for example be done by means of clausification.

\paragraph{Detransification} 
A general way of handling any transitive relation |R_| is to create a new symbol |Q_| and replace all positive occurrences of |R_| with a formula involving |Q_| (see below, positive occurrences are denoted by |+R_|); the negative occurrences are simply replaced by |~Q_|:
\begin{code}
R_ transitive       §   
T[..  pR(x,y)  ..   -->   T[..  ( Q(x,y) && (forall r . Q(r,x) => Q(r,y)) )  ..
      ~R(x,y)  ..]  §           ~Q(x,y)                                      ..]
\end{code}
We call this transformation {\em detransification}. It can be applied to any theory that involves a transitivity axiom. The transformation removes the transitivity, but adds for every positive occurrence of |R(x,y)| an implication that says ``for any |r|, if you could reach |x| from |r|, now you can reach |y| too''. Thus, we have specialized the transitivity axiom for every positive occurrence of |R_|.

Note that in the RHS theory, |Q_| does not have to be transitive! Nonetheless, the transformation is correct, meaning that it preserves (non-)satisfiability:

\begin{theorem}[Correctness of detransification] Two theories |H| and |H'| that respectively match the LHS and RHS of detransification, are equisatisfiable. 
\end{theorem}
\begin{proof}
($\Rightarrow$) If we have |m_ != H|, then |m(R_)| is transitive. Let the interpretation |m1_| interpret all existing symbols as |m_| does. Moreover, let |m1(Q_)§§(x,y) := m(R_)§§(x,y)|. We have to show that |m1(R_)§§(x,y)| implies |m1(Q_)§§(x,y)|, which is trivial, and that |m1(R_)§§(x,y)| implies |forall r . m1(Q_)§§(r,x) => m1(Q_)§§(r,y)|, which is indeed the case because |m1(R_)| is transitive. Thus we have |m1_ != H'|.

($\Leftarrow$) Assume we have |m1_ != H'|. Let the interpretation |m_| interpret all existing symbols as |m1_| does. Moreover, let |m(R_)§§(x,y) := ( m1(Q_)§§(x,y) && forall r . m1(Q_)§§(r,x) => m1(Q_)§§(r,y) )|. We have to show that |~m(Q_)§§(x,y)| implies |~m(R_)§§(x,y)|, which is the same as showing that |m(Q_)§§(x,y) && forall r . m(Q_)§§(r,x) => m(Q)§§(r,y)| implies |m(Q_)§§(x,y)|. |m(R_)| is also transitive (by transitivity of implication). Thus we also have |m != H|. |endproof|
\end{proof}

Detransification can be seen as performing one resolution step with each positive occurrence of the relation and the transitivity axiom. A positive occurrence |R(a,b)| of a transitive relation |R_|, resolved with the transitivity axiom |R(x,y) & R(y,z) => R(x,z)| becomes |R(x,a) => R(x,b)| under the substitution y := a, z := b.

\paragraph{Detransification with reflexivity} Detransification can be simplified for transitive relations that are also reflexive. In particular, we can simplify the formula with which we replace positive occurrences of the relation symbol |R_|:
\begin{code}
R_ reflexive        §     Q_ reflexive
R_ transitive       -->   
T[..  pR(x,y)  ..   §     T[..  (forall r . Q(r,x) => Q(r,y))  ..
      ~R(x,y)  ..]  §           ~Q(x,y)                        ..]
\end{code}
We now {\em replace} any positive occurrence of |R(x,y)| with an implication that says ``for any |r|, if you could reach |x| from |r|, now you can reach |y| too''. Thus, we have specialized the transitivity axiom for every positive occurrence of |R_|. The part that we omit here (namely |Q(x,y)|) is implicitly implied by the fact that |R_| is reflexive.

Similarly to the detransification transformation above, |Q_| does not have to be transitive in the RHS theory. Nonetheless, the transformation is correct, meaning that it preserves (non-)satisfiability:

\begin{theorem}[Correctness of detransification with reflexivity] Two theories |H| and |H'| that respectively match the LHS and RHS of detransification with reflexivity, are equisatisfiable. 
\end{theorem}
\begin{proof}
($\Rightarrow$) If we have |m_ != H|, then |m(R_)| is reflexive and transitive. Let the interpretation |m1_| interpret all existing symbols as |m_| does. Moreover, let |m1(Q_)§§(x,y) := m(R_)§§(x,y)|. |m1(Q_)| is obviously reflexive. We have to show that |m1(R_)§§(x,y)| implies |forall r . m1(Q_)§§(r,x) => m1(Q_)§§(r,y)|, which is indeed the case because |m1(R_)| is transitive. Thus we have |m1_ != H'|.

($\Leftarrow$) Assume we have |m1_ != H'|, then |m1(Q_)| is reflexive. Let the interpretation |m_| interpret all existing symbols as |m1_| does. Moreover, let |m(R_)§§(x,y) := ( forall r . m1(Q_)§§(r,x) => m1(Q_)§§(r,y) )|. |m(R_)| is reflexive (by reflexivity of implication) and transitive (by transitivity of implication). We have to show that |~m(Q_)§§(x,y)| implies |~m(R_)§§(x,y)|, which is the same as showing that |forall r . m(Q_)§§(r,x) => m(Q)§§(r,y)| implies |m(Q_)§§(x,y)|, which is true because |m(Q_)| is reflexive. Thus we also have |m != H|. |endproof|
\end{proof}

% ------------------------------------------------------------------------------
% - experimental results

\section{Experimental results}
We evaluate the effects of the different axiomatizations using three different resolution based theorem provers, E 2.0 \cite{E} (with the \textit{xAuto} and \textit{tAuto} options), Vampire 4.0 \cite{Vampire} (with the \textit{casc mode} option), Spass 3.9 \cite{spass}  (with the \textit{Auto} option, which activates chaining in the presence of transitive predicates), and two SMT-solvers, Z3 4.5 \cite{Z3} and CVC4 1.5 \cite{CVC4}. The experiments were performed on a PC with a 2xQuad Core Intel Xeon E5620 processor with 24 GB physical memory, running at 2.4 GHz, with Ubuntu 12.04. We use a time limit of 5 minutes on each problem.

We started from a set of 13410 test problems from the TPTP, listed as Unsatisfiable, Theorem or Unknown or Open (leaving out the very large theories)\footnote{We have also evaluated the transformations on Satisfiable/Countersatisfiable problems, but there were too few problems for the results to be significant, and the results were also mostly negative.} For each problem, a new theory was generated for each applicable transformation. For most problems, no relation matching any of the given criteria was detected, and thus no new theories were produced for these problems. In total, 2007 problems were found to include one or more transitive relations and could thus be used with at least one of the presented transformations. 130 of these problems are listed as Unknown, and an additional 172 problems have rating 1.0. No problem in the resulting set of problems is listed as Open.

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
\hspace{0.1cm}with idempotency &  &  &  +3  & -95  &  &  +6 & -13 & & +16 & -45\\&&&&&&&&&\\
ordification & (326) & 272 & n/a & n/a & 295 &  +1& -0 & 243 & n/a & n/a\\&&&&&&&&&\\
detransification  & (2007) & 1483 & \bf{+16} & -97 & 1542 &  \bf{+39} & -21 & 1200 & +91 & -91\\
\hspace{0.1cm}with reflexivity & (1359) & 1025 & +6 & -89 & 1062 &  \bf{+32} & -20 &866 & +29 & -90\\
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
\hspace{0.1cm}with idempotency &  &  & +61 & -21  &  & +44 & -26\\&&&&&&\\
ordification  & (326) & 236 & \bf{+50} & -1 & 267 & +23 & -1\\&&&&&&\\

detransification  & (2007) & 1196 & +95 & -33 & 1375 & +73 & -31\\ 
\hspace{0.1cm}with reflexivity & (1359) & 870 & +66 & -135 & 999 & +40 & -110\\ 
\end{tabular}
%\vspace{-0.5cm}
\caption{Table showing for each theorem prover the number of test problems solved before the transformation,  how many new problems are solved after the transformation, and the number of problems that could be solved before but not after the transformation. (Total number of applicable problems for each transformation in parentheses). A {\bf +value} in boldface indicates that there were hard problems (Rating 1.0) solved with that combination of treatment and theorem prover. 
}
\label{fig:overview}
\end{figure}

Overall, the results vary between each transformation and reasoning tool. For many of the transformations, we do not gain any solved problems without also losing some. A time-slicing strategy can be advantageous, were the reasoning tool is run on both the original and the transformed problem, with a suitably chosen time-limit for each. Z3 turns out to work well on ordified problems, where it can make use of its built in strategies for arithmetic. E did not benefit from any of the transformations, and a large portion of the problems became unsolvable. One may have expected better results for equalification, since introducing equality in place of each occurrence of an equivalence relation seems suitable for an equational theorem prover. However, E performs well already on the untreated problems with equivalence relations, leaving little room for improvement. Vampire has the least difference in performance before and after the transformations.

In order to make a comparison between the transformations and evaluate what transformation works best for each kind of transitive relation, we partition the test problems into different subsets (Fig. \ref{fig:subsets}). These subsets are defined by the discovered properties of the transitive relation. A problem can appear in several subsets if the problem includes several transitive relations having different properties. This is the case for 156 problems. Apart from such special cases, the subsets are disjoint. Firstly, we divide the problems into two sets, one where the transitive relation is found to be total (or strictly total, as in the case of a negated total order), and one where this was not the case. We use the notation P\textsuperscript{C} to denote the subset of problems with transitive relations with no syntactic evidence of the property P.

The problems in Total\textsuperscript{C} are further divided into four groups, depending on if they contain a transitive relation that is found to be reflexive and/or symmetric. The problems containing a total relation are partitioned into two sets: problems with one or more total order (i.e. total, transitive and antisymmetric), and problems with relations that are total and transitive but lack the antisymmetry property (labelled as "other" in the diagram). Fig. \ref{fig:subsets} shows each subset with its number of problems and number of rating 1 problems, and the transformations that are applicable for that subset. For example, a problem with a transitive relation that is in Total\textsuperscript{C}, Reflexive\textsuperscript{C} and Symmetric has the applicable transformations Pequalification and Detransification, as shown in the bottom left corner of the diagram. The number of rating 1 problems in each subset can give an indication of the difficulty of dealing with different kinds of transitive relations. Problems with equivalence relations are typically less difficult than problems with partial equivalence relations, however it is hard to tell if the difficulty of a problem is related to the transitive relation or has other reasons. 

% \begingroup

\begin{figure}[h!]
\def\mca#1{\multicolumn{1}{c}{#1}}
%\renewcommand{\arraystretch}{2.25}
%\begin{center}
\begin{tabular}{l||p{16em}||p{16em}||}
  \mca{} & \multicolumn{2}{c}{Total\textsuperscript{C}} \\\cline{2-3}
%  \multirow{6}{*}{Reflexive}               & Equivalences & Partial orders  \\\cline{2-3}
   Reflexive               & \bf{Equivalences (436/2)} & \bf{Partial orders (540/135)}  \\ %\cline{2-3}
                 & Equalification & Detransification \\
                 & Pequalification & Detransification with reflexivity \\
                 & Detransification & \\
                 & Detransification with reflexivity &  \\\cline{2-3} 
 % 
 {Reflexive\textsuperscript{C}} & \bf{Partial equivalences (181/74)} &  \bf{Strict Partial orders (607/124)}\\%\cline{2-3}
                                               & Pequalification  & Detransification\\
                                               & Detransification & \\\cline{2-3}
   \mca{} & \mca{Symmetric} & \mca{Symmetric\textsuperscript{C}} \\
    \mca{} & \mca{} & \mca{} \\
     \mca{} & \mca{} & \mca{} \\
\end{tabular}

\def\mca#1{\multicolumn{1}{c}{#1}}
\begin{tabular}{l||p{16em}||}
  \mca{} & \multicolumn{1}{c}{Total/Strictly Total} \\\cline{2-2}
  Antisymmetric/ & \bf{(Strict) Total Orders (326/28)} \\
  Strictly Antisymmetric & Ordification \\%\cline{2-2}
                         & Detransification \\\cline{2-2} 
  Antisymmetric\textsuperscript{C} & \bf{Other (73/12)} \\%\cline{2-2}
                               & Detransification \\\cline{2-2} 
  \mca{} & \mca{} 
\end{tabular}
%\end{center}
%\endgroup
\caption{Partitioning of test problems and their applicable transformations}
\label{fig:subsets}
\end{figure}

\subsection{Detransification}
Detransification is the only transformation applicable on all 2007 test problems with transitive relations. As can be seen in Fig. \ref{fig:overview}, the benefits of detransification varies with the theorem prover and problem. The SMT-solvers profit the most from this transformation, however, big differences can be seen in the different subsets.  Fig. \ref{fig:transplots} presents an overview of the effects on solving times for each theorem prover in the evaluation. For all of the theorem provers, detransification lets us prove some problems that we could not previously, but some problems also become unsolvable within the time limit.

Fig. \ref{fig:detranssubsets} presents the results of detransification on each of the subsets defined in Fig. \ref{fig:subsets}. Here we can get an indication of what problems detransification is useful for and what kind of problems tend to become harder after the transformation. For E, the results generally become worse after detransification, even though some new problems become solvable, including one with rating 1. For Vampire, detransification improves the results on problems with partial orders and partial equivalence relations. These subsets have a relatively low success rate before the transformations.  On the other subsets, the results stay fairly stable. For Spass, partial equivalences and strict partial orders benefit the most from detransification, while the other subsets show mixed results. Both SMT-solvers, Z3 and CVC4, show improved results on the transformed equivalence relations and partial equivalence relation. The theorem provers performed well on these problems already before the transformation and thus have less room for improvement. For partial orders and strict partial orders, the results are mixed, however more is gained than what is lost. Total orders and other transitive relations do not benefit from detransification using any of the reasoning tools in our evaluation.

\begin{figure}[h!]
\def\mca#1{\multicolumn{1}{c}{#1}}
%\renewcommand{\arraystretch}{2.25}
%\begin{center}
\begin{tabular}{|| l l l l || l || l l l l ||}
                 \cline{1-4} \cline{6-9} 
                 \multicolumn{4}{||l||}{\bf{Equivalences (436)}} & &  \multicolumn{4}{l||}{\bf{Partial Orders (540)}} \\
                 \cline{1-4}\cline{6-9}
                 E            & 427 & +4 & -24 & & E  & 281 & +4 & -15  \\
                 Vampire & 434 & +0 & -0 & &Vampire & 287 & \bf{+34} & -6  \\
                 Spass    & 385 & +15 & -32 & & Spass   & 201 & +15 & -16 \\
                 CVC4    & 370 & +31 & -8 &  & CVC4  & 292 & \bf{+13} & -10 \\
                 Z3         & 354 & +54 & -8 &   & Z3   & 215  & +19 & -10  
                 \\\cline{1-4} \cline{6-9}
                  \mca{} & \mca{} & \mca{} & \mca{} &  \mca{} & \mca{} & \mca{} & \mca{} \\
                \cline{1-4}\cline{6-9} 
                 \multicolumn{4}{||l||}{\bf{Partial Equivalences (181)}} & & \multicolumn{4}{l||}{\bf{Strict Partial Orders (607)}} \\
                 \cline{1-4}\cline{6-9}
                 E & 97 & \bf{+1} & -9 & & E & 421 & \bf{+5}  & -32  \\
                 Vampire & 92 & +5 & -0 & & Vampire & 444 & +5 & -11  \\
                 Spass & 67 & +8 & -0 & &  Spass & 299 & +48 & -10  \\
                 CVC4 & 51 & +16 & -0 & & CVC4 & 341 & +29 & -7  \\
                 Z3 & 38 & +18 & -0 & & Z3 & 290 & +24 & -12  \\
                \cline{1-4}\cline{6-9} 
                \mca{} & \mca{} & \mca{} & \mca{} &  \mca{} & \mca{} & \mca{} & \mca{}& \mca{} \\
                \cline{1-4}\cline{6-9} 

                 \multicolumn{4}{||l||}{\bf{Total Orders (326)  }}  & &   \multicolumn{4}{l||}{\bf{Other (73)      }}  \\
                 \cline{1-4} \cline{6-9}
                  E           & 272 & +3 & -20   & &  E & 57 & +0 & -7   \\
                 Vampire & 296 & +0 & -2   &  & Vampire & 58 & +0 & -2    \\
                 Spass    & 243 & +12 & -33   & & Spass & 47 & +2 & -0   \\
                 CVC4    & 289 & +1 & -3   &  & CVC4 & 55 & +2 & -3  \\
                 Z3         & 255 & +0 & -1   &  &  Z3 & 51 & +0 & -2    \\
                 \cline{1-4}\cline{6-9} 
\end{tabular}
%\end{center}
\caption{The effect of detransification on each subset (original number of problems solved; number of extra problems after the transformation; number of lost problems)}
\label{fig:detranssubsets}
\end{figure}

\subsection{Detransification with reflexivity}
The use of detransification with reflexivity is limited to transitive relations that are reflexive. It shows worse results than detransification without reflexivity on all applicable subsets for all of the tested tools. This is especially true for the SMT-solvers, for which many problems become unsolvable. The results on each applicable subset is shown in Fig. \ref{fig:detransreflsubsets}

\begin{figure}[h!]
\def\mca#1{\multicolumn{1}{c}{#1}}
\begin{tabular}{|| l l l l || l || l l l l ||}

                 \cline{1-4}\cline{6-9}
                \multicolumn{4}{||l||}{\bf{Equivalences (436)}} & & \multicolumn{4}{l||}{\bf{Partial Orders (540)}} \\
                 \cline{1-4}\cline{6-9}
                 E            & 427 & +3 & -30 & & E  & 281 & +1 & -20  \\
                 Vampire & 434 & +0 & -4 & & Vampire & 287 & \bf{+32} & -8  \\
                 Spass    & 385 & +14 & -44 & & Spass   & 201 & +8 & -16 \\
                 CVC4    & 370 & +32 & -45 &  & CVC4  & 292 & +5 & -55 \\
                 Z3         & 354 & +57 & -22 &  & Z3   & 215  & +12 & -41  \\
                 \cline{1-4}\cline{6-9} 
%\end{tabular}
  \mca{} & \mca{} & \mca{} & \mca{} &  \mca{} & \mca{} & \mca{} & \mca{} & \mca{} \\

%\begin{tabular}{|| l l l l || l l l l ||}
                 \cline{1-4}\cline{6-9}
                 \multicolumn{4}{||l||}{\bf{Total Orders (326)}}  & &   \multicolumn{4}{||l||}{\bf{Other (73)}}  \\
                 \cline{1-4}\cline{6-9}
                  E           & 272 & +2 & -34 & & E & 57 & +0 & -7   \\
                 Vampire & 296 & +0 & -2 &  & Vampire & 58 & +0 & -6    \\
                 Spass    & 243 & +5 & -31 & & Spass & 47 & +2 & -0   \\
                 CVC4    & 289 & +3 & -8 &  & CVC4 & 55 & +2 & -4  \\
                 Z3         & 255 & +0 & -71 &  &  Z3 & 51 & +0 & -3    \\
                 \cline{1-4}\cline{6-9} 
\end{tabular}
\caption{The effect of detransification with reflexivity on each applicable subset (original number of problems solved; number of extra problems after the transformation; number of lost problems)}
\label{fig:detransreflsubsets}
\end{figure}

\subsection{Pequalification}
Pequalification is applicable on any relation that is transitive and symmetric, i.e. both equivalence relations and partial equivalence relations. The results on these subsets are presented in Fig. \ref{fig:peqsubsets}, which also shows the results of the variant of pequalification with the added idempotency axiom. SMT-solvers benefit the most from pequalification, especially Z3 on the set of problems with equivalence relations.  All of the tested reasoning tools perform about the same or worse given this extra axiom.

Comparing pequalification with detransification, detransification is clearly much better for partial equivalence relations, while for equivalence relations it is not as clear which transformation one should pick. Pequalification without idempotency seems to be a good choice on equivalence relations for SMT-solvers, especially for Z3.

\begin{figure}[h!]
\begin{tabular}{|| l l l l || l || l l l l ||}
                 \cline{1-4}\cline{6-9}
                 \multicolumn{4}{||l||}{\bf{Equivalences (436)}}  & &  \multicolumn{4}{||l||}{\bf{Partial Equivalences (181)}}  \\
                 \cline{1-4}\cline{6-9}
                  E           & 427 & +5/+3 & -33/-59 &  & E & 97 & +0/+0 & -36/-36   \\
                 Vampire & 434 & +0/+0 & -2/-7 &  & Vampire & 92 & +5/+6 & -6/-6    \\
                 Spass    & 385 & +16/+14 & -46/-40 &  & Spass & 67 & +2/+5 & -2/-2   \\
                 CVC4    & 370 & +36/+35 & -21/-22 &   & CVC4 & 51 & +9/+9 & -4/-4  \\
                 Z3         & 354 & +59/+56 & -4/-17 &    & Z3 & 38 & +9/+7 & -4/-4    \\
                 \cline{1-4}\cline{6-9}
                 
\end{tabular} 
\caption{The effect of pequalification/pequalification with idempotency on each applicable subset (original number of problems solved; number of extra problems after the transformation; number of lost problems)}
\label{fig:peqsubsets}
\end{figure}


\subsection{Equalification}

Equalification is applicable only to problems that contain equivalence relations. It performs slightly worse or about the same compared to pequalification, which is more general. Like pequalification, it shows the best results combined with the SMT solvers. Adding an idempotency axiom typically makes the results slightly worse, with E showing the most significant change. The results of equalification and equalification with idempotency are presented in Fig. \ref{fig:eqsubsets}.

\begin{figure}[h!]
\begin{tabular}{|| l l l l ||}
                 \cline{1-4}
                 \multicolumn{4}{||l||}{\bf{Equivalences (436)}}  \\
                 \cline{1-4}
                  E           & 427 & +5/+4 & -38/-56   \\
                 Vampire & 434 & +0/+0 & -7/-6    \\
                 Spass    & 385 & +16/+14 & -46/-43   \\
                 CVC4    & 370 & +35/+35 & -20/-22   \\
                 Z3         & 354 & +60/+59 & -7/-11   \\
                 \cline{1-4} 
\end{tabular} 
\caption{The effect of equalification/equalification with idempotency on the applicable subset (original number of problems solved; number of extra problems  after the transformation; number of lost problems)}
\label{fig:eqsubsets}
\end{figure}

\subsection{Ordification} \label{subsec:ord}
Since ordification uses arithmetic, it is only applicable with Vampire (in TFF format) and Z3 and CVC4 (in SMT format). The original problems were transformed into TFF and SMT as well, in order to achieve a fair comparison, avoiding the effects that the change of input format may have on the results. Ordification is applicable only on the set of problems containing total orders. Ordification improved the results significantly for both Z3 and CVC4, while Vampire performs about the same as before the transformation.

\begin{figure}[h!]
\begin{tabular}{|| l l l l ||}
                 \cline{1-4}
                 \multicolumn{4}{||l||}{\bf{Total Orders (326)}}  \\
                 \cline{1-4}
                 Vampire & 295 & +1 & -0   \\
                 CVC4    & 288 & +1 & -1   \\
                 Z3         & 254 & +50 & -1   \\
                 \cline{1-4} 
\end{tabular} 
\caption{The effect of ordification on the applicable subset (original number of problems solved; number of extra problems after the transformation; number of lost problems)}
\label{fig:ordsubset}
\end{figure}

We can compare ordification with detransification, which is the only other transformation that is applicable on total orders. Similarly to ordification, detransification does not have any significant impact on the results for either of CVC4 or Vampire on total orders. For Z3, ordification is clearly the best choice. Note however that Z3 shows worse results than CVC4 and Vampire prior to the transformation. After ordification, the three tools solve about the same number of problems. The results are presented in Fig. \ref{fig:ordsubset}.

\subsection{Problems with more than one kind of transitive relation}
156 of the problems in our evaluation contain more than one kind of transitive relation. 140 of them contain a partial equivalence relation and a strict partial order. 14 contain an equivalence relation and a partial order, and two problems contain a partial equivalence relation and a relation that is total and transitive. Almost half of these problems are hard, with rating 1 in the TPTP.

For the 140 problems with a partial equivalence and a strict partial order, we found that applying detransification to all of the transitive relations gave the best results. 
For the 14 problems with equivalence relation and a partial order, applying equalification on the equivalence relation and detransification on the partial order was the best, in particular for the SMT-solvers. The 2 remaining problems with multiple kinds of transitive relations are both labelled as Unknown, and were not solved before nor after any choice of transformation.

\subsection{Time-slicing}

As can be seen in Fig. \ref{fig:transplots} - \ref{fig:ordifiedplots}, problems are typically solved within the first half of the five minute time-limit or less. By splitting the time equally between the original version of the problem and the applicable transformations can thus in many cases improve the success rate. This was the case for Spass, CVC4 and Z3. For Vampire (which has its own built-in time-slicing strategies), many problems were solved towards the end of the five minutes, and time-slicing between transformations was thus less favourable. For E, whose advantages of the transformations were quite limited, the problems that did become solvable after a transformation were solved in a relatively short time. The best results were achieved by allowing 10 seconds on each applicable transformation, and the remaining time on the original problem.

\subsection{Optimal strategies}

We present for each tool an optimal strategy, that is given by identifying for each subset the transformation or combination of transformations that maximises the total number of solved problems. Since the results are based on the limited set of problems in the current TPTP library, we do not provide a universal method, but rather an idea of how parameters can be tuned to improve the results. 

In section \ref{subsec:ord}, we transformed the original problem into the same format as the ordified problem (SMT format for Z3 and CVC4, and TFF format for Vampire), to focus on the effects of ordification alone. In this section we are concerned with how the results of the problems in the TPTP library can be improved. We therefore compare all results of the transformations (including ordification) with the original TPTP problem given in CNF-format. This makes a difference for Z3, which performs better on the original problems in CNF format than the problems transformed into SMT. This is the reason why Z3 solves 31 new problems after ordification in Fig. \ref{fig:z3_ord}  but 50 new problems in Fig. \ref{fig:ordsubset}. We omit detransification with reflexivity and the idempotency version of equalification and pequalification in the diagrams below, as these transformations did not contribute to the overall results.

\subsubsection{E}
E did not have any major benefits from any of the transformations. However, with time-slicing we can avoid a lot of the bad effects of a transformation, while still keeping the results that were improved. For E, the best results were achieved when allowing 10 seconds on each transformed problem and the remaining time on the original problem. This is based on a time-limit of 5 minutes. Fig. \ref{fig:e_subs} show the subsets on which there was a transformation that solved new problems. With this strategy, we gain a total of 10 solved problems, 7 with equivalence relations and 3 with partial orders. On the remaining subsets there is no transformation that increases the success rate compared to the original, but splitting does not decrease it. 

\begin{figure}[h!]
\def\mca#1{\multicolumn{1}{c}{#1}}
\begin{tabular}{|| l l ||}
                 \cline{1-2}
                 \multicolumn{2}{||l||}{\bf{Equivalences (436)}}  \\
                 \cline{1-2}
                 original & 427   \\
                 equalification & 394 (+5 - 38) \\
                 pequalification &  399 (+5 -33) \\
                 detransification & 407 (+4 -24)\\
                   % with reflexivity & 400 (+3 -30)\\
                 original 270 / equalification 10 & 434 (+7  -0)\\
                 pequalification 10 / detransification 10 & \\
                 original 75 / equalification 75 & 434 (+7  -6)\\
                 pequalification 75 / detransification 75 & \\
                 \cline{1-2} 
                 \mca{} & \mca{}
\end{tabular} 
%\caption{Results of E on problems with equivalence relations}
%\label{fig:e_eq}
%\end{figure}

%\begin{figure}[h!]
\begin{tabular}{|| l l ||}
                 \cline{1-2}
                 \multicolumn{2}{||l||}{\bf{Partial Orders (540)}}  \\
                 \cline{1-2}
                 original & 281   \\
                 detransification & 270 (+4 -15)\\
                 original 290 / detransification 10 & 284 (+3  -0)\\
                 original 150 / detransification 150 & 282 (+4 -3)\\
                   \cline{1-2} 
\end{tabular} 
\caption{Results of E by subset and strategy (number of problems solved; number of extra/lost problems in parentheses)}
\label{fig:e_subs}
\end{figure}

\subsubsection{Vampire}
For Vampire, detransification is the best choice for both partial orders and partial equivalence relations. A majority of the problems solved after detransification but not before took a long time, making time-slicing less favorable. For the other subsets, Vampire is the most successful on the original problems. Using detransification on partial equivalences and partial orders, and no transformation otherwise, we gain 39 solved problems and lose 6.

\begin{figure}[h!]
\def\mca#1{\multicolumn{1}{c}{#1}}
\begin{tabular}{|| l l ||}
                 \cline{1-2}
                 \multicolumn{2}{||l||}{\bf{Partial Equivalences (181)}}  \\
                 \cline{1-2}
                 original & 92   \\
                 pequalification & 91 (+5 -6)\\
                 detransification & 97 (+5 -0)\\
                 original 290 / detransification 10 & 92 (+0  -0)\\
                 original 150 / detransification 150 & 93 (+1 -0)\\       
                   \cline{1-2} \\
                  \mca{} & \mca{}\\
%\end{tabular} 
%\label{fig:vamp_peq}
%\begin{tabular}{|| l l ||}
                 \cline{1-2}
                 \multicolumn{2}{||l||}{\bf{Partial Orders (540)}}  \\
                 \cline{1-2}
                 original & 287   \\
                 detransification & 315 (+34 -6)\\
                 original 290 /detransification 10 & 301 (+14  -0)\\
                 original 150 / detransification 150 & 308 (+24 -3)\\
                   \cline{1-2} 
\end{tabular} 
\caption{Results of Vampire by subset and strategy (number of problems solved; number of extra/lost problems in parentheses)}
\label{fig:vamp_pos}
\end{figure}

\subsubsection{Spass}
For Spass, the best results for transitive and reflexive relations (i.e. equivalences and partial orders) were given by spending 10 seconds on each of the applicable transformations, and the remaining time on the original problem. For the remaining subsets, splitting evenly between the applicable transformations and untransformed problems solves the most problems. The 8 new solved problems with a partial equivalence also have a strict partial order, and thus are contained in the 43 new problems that were solved in the partial orders subset. In total, the optimal strategy solves 75 new problems, while it loses 15.
 
\begin{figure}[h!]
\def\mca#1{\multicolumn{1}{c}{#1}}
\begin{tabular}{|| l l ||}
                 \cline{1-2}
                 \multicolumn{2}{||l||}{\bf{Equivalences (436)}}  \\
                 \cline{1-2}
                 original & 385   \\
                 equalification & 355 (+16 - 46) \\
 %                pequalification &  355 (+16 -46) \\
                 detransification & 392 (+15 -8)\\
 %                  with reflexivity & 391 (+14 -8)\\
                 original 270 / equalification 10 & 403 (+18  -0)\\
                 pequalification 10 / detransification 10& \\
                 original 75 / equalification 75 & 398 (+18  -5)\\
                 pequalification 75 / detransification 75& \\
                 \cline{1-2} 
                  \mca{} & \mca{} 
                  \end{tabular} 
%\end{figure}

%\begin{figure}
\begin{tabular}{|| l l ||}
                 \cline{1-2}
                 \multicolumn{2}{||l||}{\bf{Partial Equivalences (181)}}  \\
                 \cline{1-2}
                 original & 67   \\
                 pequalification & 61 (+0 -36)\\
                 detransification & 75 (+8 -0)\\
                 original 280 /  pequalification 10  & 69 (+3  -1)\\  
                  /detransification 10 & \\
                 original 100 /  pequalification 100  & 75 (+8  -0)\\ 
                  /detransification 100 & \\
                   \cline{1-2} 
                   \mca{} & \mca{}
\end{tabular} 
\label{fig:spass_peq}
%\end{figure}

%\begin{figure}[h!]
\begin{tabular}{|| l l ||}
                 \cline{1-2}
                 \multicolumn{2}{||l||}{\bf{Partial Orders (540)}}  \\
                 \cline{1-2}
                 original & 201   \\
                 detransification & 200 (+15 -16)\\
                 original 290 / detransification 10 & 208 (+7  -0)\\
                 original 150 / detransification 150 & 204 (+11  -8)\\
                   \cline{1-2} 
                   \mca{} & \mca{}
\end{tabular} 
\label{fig:spass_pos}
%\end{figure}

%\begin{figure}[h!]
\begin{tabular}{|| l l ||}
                 \cline{1-2}
                 \multicolumn{2}{||l||}{\bf{Strict Partial Orders (607)}}  \\
                 \cline{1-2}
                 original & 299   \\
                 detransification & 337 (+48 -10)\\
                 original 290 /detransification 10 & 322 (+24 -1)\\
                 original 150 /detransification 150 & 339 (+43 - 3)\\
                   \cline{1-2} 
                   \mca{} & \mca{}
\end{tabular} 
\label{fig:spass_spos}
%\end{figure}

%\begin{figure}[h!]
\begin{tabular}{|| l l ||}
                 \cline{1-2}
                 \multicolumn{2}{||l||}{\bf{Total Orders (326)}}  \\
                 \cline{1-2}
                 original & 243   \\
                 detransification & 222 (+12 -33)\\
                 original 290 / detransification 10 & 245 (+2  -0)\\
                  original 150 / detransification 150 & 251 (+12  -4)\\
                   \cline{1-2} 
                   \mca{} & \mca{}
\end{tabular} 
\label{fig:spass_ord}
%\end{figure}

%\begin{figure}[h!]
\begin{tabular}{|| l l ||}
                 \cline{1-2}
                 \multicolumn{2}{||l||}{\bf{Other (73)}}  \\
                 \cline{1-2}
                 original & 47   \\
                 detransification & 49 (+2 -0)\\
                 original 290 /detransification 10 & 47 (+0  -0)\\
                 original 150 /detransification 150 & 48 (+1 -0)\\	
                  \cline{1-2} 
                  \mca{} & \mca{}
\end{tabular} 
\caption{Results of Spass by subset and strategy (number of problems solved; number of extra/lost problems in parentheses)}
\label{fig:spass_other}
\end{figure}

\subsubsection{Z3}
For Z3, the best strategy is to split the time evenly between the original problem and all of the applicable transformations. Spending 10 seconds on each applicable transformation and the remaining time on the original problem gives very similar results. In total, we solve 135 new problems compared to the original, and lose 6. 21 of the newly solved problems are in overlapping subsets (containing more than one kind of transitive relation).

\begin{figure}[h!]
\def\mca#1{\multicolumn{1}{c}{#1}}
\begin{tabular}{|| l l ||}
                 \cline{1-2}
                 \multicolumn{2}{||l||}{\bf{Equivalences (436)}}  \\
                 \cline{1-2}
                 original & 354   \\
                 equalification & 407 (+60 - 7) \\
                 pequalification &  409 (+59 -4) \\
                 detransification & 400 (+54 -8)\\
          %         with reflexivity & 389 (+57 -22)\\
       %          original 290 / (p)equalification 10 & 412 (+58  -0)\\
          %       original 290 / detransification 10 & 406 (+52 -0)\\
                 original 270 / equalification 10 & 417 (+63  -0)\\
                 pequalification 10 /detransification 10& \\ 
                 original 75 / equalification 75 & 417 (+64  -1)\\
                 pequalification 75 /detransification 75& \\ 
                 \cline{1-2} 
                 \mca{} & \mca{}
\end{tabular} 
\label{fig:z3_eq}

\begin{tabular}{|| l l ||}
                 \cline{1-2}
                 \multicolumn{2}{||l||}{\bf{Partial Equivalences (181)}}  \\
                 \cline{1-2}
                 original & 38   \\
                 pequalification & 43 (+9 -4)\\
                 detransification & 56 (+18 -0)\\
             %    original 290 /detransification 10 & 55 (+17  -0)\\
                 original 280 /detransification 10  & 57 (+19 -0) \\
                 pequalification 10 & \\
                 original 100 /detransification 100  & 59 (+21 -0) \\
                 pequalification 100  & \\
                   \cline{1-2} 
                   \mca{} & \mca{}
\end{tabular} 
\label{fig:z3_peq}

\begin{tabular}{|| l l ||}
                 \cline{1-2}
                 \multicolumn{2}{||l||}{\bf{Partial Orders (540)}}  \\
                 \cline{1-2}
                 original & 215   \\
                 detransification & 224 (+19 -10)\\
                 original 290 /detransification 10 & 229 (+14  -0)\\
                 original 150 /detransification 150 & 230 (+18  -3)\\
                   \cline{1-2} 
                   \mca{} & \mca{}
\end{tabular} 
\label{fig:z3_pos}

\begin{tabular}{|| l l ||}
                 \cline{1-2}
                 \multicolumn{2}{||l||}{\bf{Strict Partial Orders (607)}}  \\
                 \cline{1-2}
                 original & 290   \\
                 detransification & 302 (+24 -12)\\
                 original 290 /detransification 10 & 312 (+22 -0)\\
                 original 150 /detransification 150 & 311 (+23 -2)\\
                   \cline{1-2} 
                   \mca{} & \mca{}
\end{tabular} 
\label{fig:z3_spos}

\begin{tabular}{|| l l ||}
                 \cline{1-2}
                 \multicolumn{2}{||l||}{\bf{Total Orders (326)}}  \\
                 \cline{1-2}
                 original & 255   \\
                 detransification & 254 (+0 -1)\\
                 ordification & 285 (+31 -1)\\
                 original 290 /detransification 10 & 282 (+27  -0)\\
                  ordification 10 &\\
                 original 100 /detransification 100 & 285 (+30  -0)\\
                  ordification 100 &\\
                    \cline{1-2} 
                    \mca{} & \mca{}
\end{tabular} 

\begin{tabular}{|| l l ||}
                 \cline{1-2}
                 \multicolumn{2}{||l||}{\bf{Other (73)}}  \\
                 \cline{1-2}
                 original & 51   \\
                 detransification & 49 (+0 -2)\\
                 original 290 /detransification 10 & 51 (+0  -0)\\
                 original 150 /detransification 150 & 51 (+0  -0)\\
                  \cline{1-2} 
                  \mca{} & \mca{}
\end{tabular} 
\caption{Results of Z3 by subset and strategy (number of problems solved; number of extra/lost problems in parentheses)}
\label{fig:z3_ord}
\end{figure}



\subsubsection{CVC4}
 For CVC4, splitting evenly between the original problem and all of the applicable transformations gives the best results. 19 of the newly solved problems are overlapping; 16 problems have both a partial equivalence and a strict partial order. 3 of the problems have an equivalence relation and a partial order. The total gain of the optimal strategy is 83 problems, and the loss is 2 problems.

\begin{figure}[h!]
\def\mca#1{\multicolumn{1}{c}{#1}}
\begin{tabular}{|| l l ||}
                 \cline{1-2}
                 \multicolumn{2}{||l||}{\bf{Equivalences (436)}}  \\
                 \cline{1-2}
                 original & 370   \\
                 equalification & 385 (+35 - 20) \\
                 pequalification &  385 (+36 -21) \\
                 detransification & 393 (+31 -8)\\
           %        with reflexivity & 357 (+32 -45)\\
    %             original 290 / equalification 10 & 405 (+35  -0)\\
      %           original 290 / detransification 10 & 396 (+26 -0)\\
                 original 270 / equalification 10 & 410 (+40  -0)\\
                 pequalification 10 /detransification 10& \\
                 original 75 / equalification 75 & 412 (+42  -0)\\
                 pequalification 75 /detransification 75& \\
                 \cline{1-2} 
                 \mca{} & \mca{}
\end{tabular} 
\label{fig:cvc4_eq}

\begin{tabular}{|| l l ||}
                 \cline{1-2}
                 \multicolumn{2}{||l||}{\bf{Partial Equivalences (181)}}  \\
                 \cline{1-2}
                 original & 51   \\
                 pequalification & 56 (+9 -4)\\
                 detransification & 67 (+16 -0)\\
                 original 280 / detransification 10  & 65 (+14 -0) \\
                 pequalification 10 &\\
                 original 100 / detransification 100  & 67 (+16 -0) \\
                 pequalification 100 &\\
                   \cline{1-2} 
                    \mca{} & \mca{}
\end{tabular} 
\label{fig:cvc4_peq}

\begin{tabular}{|| l l ||}
                 \cline{1-2}
                 \multicolumn{2}{||l||}{\bf{Partial Orders (540)}}  \\
                 \cline{1-2}
                 original & 292   \\
                 detransification & 295 (+13 -10)\\
                 original 290 / detransification 10 & 302 (+10  -0)\\
                 original 150 / detransification 150 & 304 (+12  -0)\\
                   \cline{1-2} 
                   \mca{} & \mca{}
\end{tabular} 
\label{fig:cvc4_pos}

\begin{tabular}{|| l l ||}
                 \cline{1-2}
                 \multicolumn{2}{||l||}{\bf{Strict Partial Orders (607)}}  \\
                 \cline{1-2}
                 original & 341   \\
                 detransification & 363 (+29 -7)\\
                 original 290 / detransification 10 & 360 (+19 -0)\\
                 original 150 / detransification 150 & 368 (+29 -1)\\
                   \cline{1-2} 
                  \mca{} & \mca{}
\end{tabular} 
\label{fig:cvc4_spos}

\begin{tabular}{|| l l ||}
                 \cline{1-2}
                 \multicolumn{2}{||l||}{\bf{Total Orders (326)}}  \\
                 \cline{1-2}
                 original & 289   \\
                 detransification & 287 (+1 -3)\\
                 ordification & 288 (+0 -1)\\
                 original 290 / detransification 10 & 290 (+1  -0)\\
                  ordification 10  & \\  
                  original 100 / detransification 100 & 290 (+1  -0)\\
                  ordification 100  & \\  
                  \cline{1-2} 
                  \mca{} & \mca{}
\end{tabular} 
\label{fig:cvc4_ord}

\begin{tabular}{|| l l ||}
                 \cline{1-2}
                 \multicolumn{2}{||l||}{\bf{Other (73)}}  \\
                 \cline{1-2}
                 original & 55   \\
                 detransification & 54 (+2 -3)\\
                 original 290 /detransification 10 & 56 (+1  -0)\\
                 original 150 /detransification 150 & 56 (+2  -1)\\
                  \cline{1-2} 
                  \mca{} & \mca{}
\end{tabular} 
\caption{Results of CVC4 by subset and strategy (number of problems solved; number of extra/lost problems in parentheses)}
\label{fig:cvc4_other}
\end{figure}


\section{Discussion and Conclusions}

We have presented 6 transformations that can be applied to theories with certain transitive relations: equalification, pequalification, ordification, maxification, detransification, and detransification with reflexivity. We have also created a method for syntactic discovery of binary relations where these transformations are applicable.

For users of reasoning tools that create their own theories, it is clear that they should consider using one or more of the proposed alternative treatments when writing theories. For all of our methods, there are existing theories for which some provers performed better on these theories than others. In particular, there exist 5 TPTP problems that are now solvable that weren't previously. These are FLD012-2 (solved by E with detransification), SEU322+2 (Solved by Vampire and Z3 with detransification), SEU270+2 (solved by CVC4 and Z3 with detransification), SEU372+2 (solved by Vampire with detransification) and LDA005-1 (solved by Z3 with ordification).

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
\label{fig:transplots}
\end{figure}

\begin{figure}[t!]
\includegraphics[scale=0.65,trim=10mm 00mm 20mm 0mm]{Plots/Trans_Ref/E/test_original_e_transified_e_300.eps}
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/Trans_Ref/Vampire/test_original_vampire_transified_vampire_300.eps}\\
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/Trans_Ref/Spass/test_original_spass_transified_spass_300.eps} 
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/Trans_Ref/Z3/test_original_z3_transified_z3_300.eps} \\
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/Trans_Ref/CVC4/test_original_cvc4_transified_cvc4_300.eps}
\caption{Effects of transification with reflexivity, using E, Vampire, Spass, Z3 and CVC4 }
\label{fig:transrefplots}
\end{figure}

\begin{figure}[h!]
\includegraphics[scale=0.65,trim=10mm 00mm 20mm 0mm]{Plots/Equalified/E/test_original_e_equalified_e_300.eps}
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/Equalified/Vampire/test_original_vampire_equalified_vampire_300.eps}\\
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/Equalified/Z3/test_original_z3_equalified_z3_300.eps}
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/Equalified/CVC4/test_original_cvc4_equalified_cvc4_300.eps}\\
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/Equalified/Spass/test_original_spass_equalified_spass_300.eps}
\caption{The time taken to solve problems, with and without equalification, using E, Vampire, Z3 and CVC4 }
\label{fig:equalifiedplots}
\end{figure}

\begin{figure}[h!]
\includegraphics[scale=0.65,trim=10mm 00mm 20mm 0mm]{Plots/PEqualified/E/test_original_e_pequalified_e_300.eps}
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/PEqualified/Vampire/test_original_vampire_pequalified_vampire_300.eps}\\
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/PEqualified/Z3/test_original_z3_pequalified_z3_300.eps}
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/PEqualified/CVC4/test_original_cvc4_pequalified_cvc4_300.eps}\\
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/PEqualified/Spass/test_original_spass_pequalified_spass_300.eps}
\caption{The time taken to solve problems, with and without pequalification, using E, Vampire, Spass, Z3 and CVC4 }
%\includegraphics[scale=0.22]{Plots/Equalified/E/}
%\end{figure}
\label{fig:pequalifiedplots}
\end{figure}

\begin{figure}[h!]
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/Ordified/Vampire/test_original_vampire_ordified_vampire_300.eps}\\
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/Ordified/Z3/test_original_z3_ordified_z3_300.eps}
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/Ordified/CVC4/test_original_CVC4_ordified_cvc4_300.eps}\\
\caption{The time taken to solve problems, with and without ordification, using Vampire, Z3 and CVC4 }
%\includegraphics[scale=0.22]{Plots/Equalified/E/}
%\end{figure}
\label{fig:ordifiedplots}
\end{figure}

% ------------------------------------------------------------------------------
% - references

\bibliographystyle{plain}
\bibliography{main}

\end{document}

