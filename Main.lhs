\documentclass{easychair}
\usepackage{amssymb}
\usepackage{mathabx}
\usepackage{subcaption}
%include polycode.fmt

 \def\comment#1{$\Rightarrow$ {\em #1} $\Leftarrow$}


% ------------------------------------------------------------------------------
% - title and stuff

\title{Alternative Treatments\\of Common Transitive Relations\\in First-Order Automated Reasoning}

\titlerunning{Alternative Treatments of Common Transitive Relations}

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
% - some commands

\newcommand{\parag}[1]{\vspace{0.2cm}\noindent {\bf #1} $\;\;$}

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

%format R  = "R\hspace{-0.1cm}"
%format R_ = "R"

%format Q  = "Q\hspace{-0.1cm}"
%format Q_ = "Q"

%format rep  = "rep\hspace{-0.1cm}"
%format rep_ = "rep"

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
We present a number of alternative ways of treating transitive binary relations that commonly occur in first-order problems, in particular {\em equivalence relations}, {\em total orders}, and {\em reflexive, transitive relations}. We show how such relations can be discovered syntactically in an input theory. We experimentally evaluate different treatments on problems from the TPTP, using resolution-based reasoning tools as well as instance-based tools. Our conclusions are that (1) it is beneficial to consider different treatments of binary relations as a user, and that (2) reasoning tools could benefit from using a preprocessor or even built-in support for certain binary relations.
\end{abstract}

% ------------------------------------------------------------------------------
% - introduction

\section{Introduction}

Most automated reasoning tools for first-order logic have some kind of built-in support for reasoning about equality. Why? Because equality is one of the most common binary relations, and there are great performance benefits from providing built-in support for equality. Together, these two advantages by far outweigh the cost of implementation.

Other common concepts for which there exists built-in support in many tools are associative, commutative operators; and real-valued, rational-valued, and integer-valued arithmetic. Again, these concepts seem to appear often enough to warrant the extra cost of implementing special support in reasoning tools.

This paper is concerned with investigating what kind of special treatment we could give to commonly appearing transitive binary relations, and what effect this treatment has in practice. Adding special treatment of transitive relations to reasoning tools has been the subject of study before, in particular by means of {\em chaining} \cite{chaining}. The transitivity axiom
\begin{code}
forall x,y,z . R(x,y) && R(y,z) => R(x,z)
\end{code}
can lead to an expensive proof exploration in resolution and superposition based theorem provers, and can generate a huge number of instances in instance-based provers and SMT-solvers. Transitive relations are also common enough to motivate special built-in support. However, as far as we know, chaining is not implemented in any of the major first-order reasoning tools (at least not in E \cite{E}, Vampire \cite{Vampire}, Z3 \cite{Z3}, and CVC4 \cite{CVC4}, which were used in this paper).

As an alternative to adding built-in support, in this paper we mainly look at (1) what a user of a reasoning tool may do herself to optimize the treatment of these relations, and (2) how a preprocessing tool may be able to do this automatically. Adding built-in reasoning support in the tools themselves is not a main concern of this paper.

By ``treatment'' we mean any way of logically expressing the relation. For example, a possible treatment of a binary relation |R_| in a theory |T| may simply mean axiomatizing |R_| in |T|. But it may also mean transforming |T| into a satisfiability-equivalent theory |T'| where |R_| does not even syntactically appear.

As an example, consider a theory |T| in which an equivalence relation |R_| occurs. One way to deal with |R_| is to simply axiomatize it, by means of reflexivity, symmetry, and transitivity:
\begin{code}
forall x      . R(x,x)
forall x,y    . R(x,y) => R(y,x)
forall x,y,z  . R(x,y) && R(y,z) => R(x,z)
\end{code}
Another way is to ``borrow'' the built-in equality treatment that exists in most theorem provers. We can do this by introducing a new symbol |rep_|, and replacing all occurrences of |R_| by the formula:
\begin{code}
rep(x)=rep(y)
\end{code}
The intuition here is that |rep_| is now the representative function of the relation |R_|. No axioms are needed. As we shall see, this alternative treatment of equivalence relations is satisfiability-equivalent with the original one, and actually is beneficial in practice in certain cases.

In general, when considering alternative treatments, we strive to make use of concepts already built-in to the reasoning tool in order to express other concepts that are not built-in.

For the purpose of this paper, we have decided to focus on three different kinds of transitive relations: (1) {\em equivalence relations} and {\em partial equivalence relations}, (2) {\em total orders} and {\em strict total orders}, and (3) {\em reflexive, transitive relations}. The reason we decided to concentrate on these three are because (a) they appear frequently in practice, and (b) we found well-known ways but also novel ways of dealing with these.

The target audience for this paper is thus both people who use reasoning tools and people who implement reasoning tools.

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
\end{center}
\vspace{-0.5cm}
\caption{Number of occurrences of binary relation properties in TPTP}
\label{fig:occurs}
\end{figure}

When we investigated the number of occurrences of these properties in a subset of the TPTP problem library\footnote{For the statistics in this paper, we decided to only look at unsorted TPTP problems with 10.000 clauses or less.} \cite{tptp}, we ended up with the table in Fig.\ \ref{fig:occurs}. The table was constructed by gathering all clauses from all TPTP problems (after clausification), and keeping every clause that only contained one binary relation symbol and, possibly, equality. Each such clause was then categorized as an expression of a basic property of a binary relation symbol. We found only 163 such clauses that did not fit any of the 8 properties we chose as basic properties, but were instead instances of two new properties. Both of these were quite esoteric and did not seem to have a standard name in mathematics.

The table also contains occurrences where a {\em negated relation} was stated to have a certain property, and also occurrences where a {\em flipped relation} (a relation with its arguments swapped) was stated to have a certain property, and also occurrences of combined negated and flipped relations. This explains for example why the number of occurrences of {\em total} relations is the same as for {\em asymmetric} relations; if a relation is total, the negated relation is asymmetric and vice-versa.

We adopt the following notation. Given a property of binary relations |prop|, we introduce its {\em negated version}, which is denoted by |prop^~|. The property |prop^~| holds for |R_| if and only if |prop| holds for |~R_|. Similarly, we introduce the {\em flipped version} of a property |prop|, which is denoted by |prop^^|. The property |prop^^| holds for |R_| if and only if |prop| holds for the flipped version of |R_|.

Using this notation, we can for example say that |total| is equivalent with |asymmetric^~|. Sometimes the property we call |euclidean| here is called |right euclidean|; the corresponding variant |left euclidean| can be denoted |euclidean^^|. Note that |prop^~| is not the same as |~prop|! For example, a relation |R_| can be |reflexive|, or |reflexive^~| (which means that |~R_| is reflexive), or |~reflexive|, which means that |R_| is not reflexive.

Using this notation on the 8 original basic properties from Fig.\ \ref{fig:props}, we end up with 32 new basic properties that we can use. (However, as we have already seen, some of these are equivalent to others.)

This paper will look at 5 kinds of different binary relations, which are defined as combinations of basic properties:
\begin{code}
equivalence relation            ==  {reflexive, symmetric, transitive}
partial equivalence relation    ==  {symmetric, transitive}
total order                     ==  {total, antisymmetric, transitive}
strict total order              ==  {antisymmetric^~, asymmetric, transitive}
reflexive, transitive relation  ==  {reflexive, transitive}
\end{code}
As a side note, in mathematics, strict total orders are sometimes defined using a property called {\em trichotomous}, which means that exactly one of |R(x,y)|, |x=y|, or |R(y,x)| must be true. However, when you clausify this property in the presence of transitivity, you end up with |antisymmetric^~| which says that at least one of |R(x,y)|, |x=y|, or |R(y,x)| must be true. There seems to be no standard name in mathematics for the property |antisymmetric^~|, which is why we use this name.

% \comment{Should I include sat/csat/unknown/open in the table?}
\begin{figure}[t]
\begin{center}
\begin{tabular}{rl}
429+19 & equivalence relations \\
117+72 & partial equivalence relations \\
327+8 & (strict) total orders \\
545+4 & reflexive, transitive relations (excluding the above)\\
\end{tabular}
\end{center}
\vspace{-0.5cm}
\caption{Number of occurrences of common combinations of basic binary relation properties in TPTP}
\label{fig:occurs2}
\end{figure}

In Fig.\ \ref{fig:occurs2}, we display the number of binary relations we have found in (our subset of) the TPTP for each category. The next section describes how we found these.

% ------------------------------------------------------------------------------
% - discovering relations

\section{Syntactic discovery of common binary relations} \label{sec:discovery}

If our goal is to automatically choose the right treatment of equivalence relations, total orders, etc., we must have an automatic way of identifying them in a given theory. It is easy to discover for example an equivalence relation in a theory by means of syntactic inspection. If we find the presence of the axioms |reflexive|, |symmetric|, and |transitive|, for the same relational symbol |R_|, we know that |R_| is a binary relation.

But there is a problem. There are other ways of axiomatizing equivalence relations. For example, a much more common way to axiomatize equivalence relations in the TPTP is to state the two properties |reflexive| and |euclidean| for |R_|\footnote{A possible reason for this is a paper written in the 1990s that argued for this alternative axiomatization. The first author of this paper has at one point seen this paper, but at the time of the writing, we have not been able to find it again! If any reviewer knows which paper we are talking about, help would be appreciated.}. 

Rather than enumerating all possible ways to axiomatize certain relations by hand, we wrote a program that computes all possible ways for any combination of basic properties to imply any other combination of basic properties. Our program generates a table (shown in Appendix \ref{sec:implications}) that can be precomputed in a minute or so and used to very quickly detect any alternative axiomatization of binary relations using basic properties.

\begin{figure}[t]
\begin{center}
%include Implications/equivalences.tex
\end{center}
\vspace{-0.5cm}
\caption{Basic properties that are equivalent}
\label{fig:equivs}
\end{figure}

Let's explain how this table was generated. We start with a list of 32 basic properties (the 8 original basic properties, plus their negated, flipped, and negated flipped versions). Firstly, we use an automated theorem prover (we used E \cite{eprover}) to discover which of these are equivalent with other such properties. The result is displayed in Fig.\ \ref{fig:equivs}. Thus, 17 basic properties can be removed from the list, because they can be expressed using other properties. The list of basic properties now has 15 elements left.

Secondly, we want to generate all implications of the form |{prop1, .., propn} => prop| where the set |{prop1, .., propn}| is minimal. We do this separately for each |prop|. (The results are displayed in Appendix \ref{sec:implications}.)

The procedure uses a simple constraint solver (a SAT-solver) to keep track of all implications it has tried so far, and consists of one main loop. At every loop iteration, the constraint solver guesses a set |{prop1, .., propn}| from the set of all properties |P-{prop}|. The procedure then asks E whether or not |{prop1, .., propn} => prop| is valid. If it is, then we look at the proof that E produces, and print the implication |{propa, .., propb} => prop|, where |{propa, .., propb}| is the subset of properties that were used in the proof. We then also tell the constraint solver never to guess a superset of |{propa, .., propb}| again. If the guessed implication can not be proven, we tell the constraint solver to never guess a subset of |{prop1, .., propn}| again. The procedure stops when no guesses that satisfy all constraints can be made anymore.

After the loop terminates, we may need to clean up the implications somewhat because some implications may subsume others.

In order to avoid generating inconsistent sets |{prop1, .., propn}| (that would imply any other property), we also add the artificial inconsistent property |false| to the set, and generate implications for this property first. We exclude any found implication here from the implication sets of the real properties. 

This procedure generates a complete list of minimal implications. It works well in practice, especially if all guesses are maximized according to their size. The vast majority of the time is spent on the implication proofs, and no significant time is spent in the SAT-solver.

To detect a binary relation |R_| with certain properties in a given theory, we simply gather all basic properties about |R_| that occur in the theory, and then compute which other properties they imply, using the pre-generated table. In this way, we never have to do any theorem proving in order to detect a binary relation with certain properties.

% ------------------------------------------------------------------------------
% - equivalence relations

\section{Dealing with equivalence relations}

\parag{Equalification} As mentioned in the introduction, an alternative way of dealing with equivalence relations |R_| is to create a new symbol |rep_| and replace all occurrences of |R_| with a formula involving |rep_|:
\begin{code}
R_ reflexive     §    
R_ symmetric     -->   §
R_ transitive    §
T[.. R(x,y) ..]  §     T[.. rep(x)=rep(y) ..]
\end{code}
To explain the above notation: We have two theories, one on the left-hand side of the arrow, and one on the right-hand side of the arrow. The transformation transforms any theory that looks like the left-hand side into a theory that looks like the right-hand side. We write |T[.. e ..]| for theories in which |e| occurs syntactically; in the transformation, all occurrences of |e| should be replaced.

We call the above transformation {\em equalification}. Doing so may be beneficial because the reasoning now involves built-in equality reasoning instead of reasoning about an unknown symbol using axioms.

The transformation is correct, meaning that it preserves (non-)satisfiability: ($\Rightarrow$) If we have a model of the LHS theory, then |R_| must be interpreted as an equivalence relation. Let |rep_| be the representative function of |R_|, in other words we have |R(x,y) <=> rep(x)=rep(y)|. Thus we also have a model of the RHS theory. ($\Leftarrow$) If we have a model of the RHS theory, let |R(x,y):=rep(x)=rep(y)|. It is clear that |R_| is reflexive, symmetric, and transitive, and therefore we have model of the LHS theory.

In the transformation, we also remove the axioms for reflexivity, symmetry, and transitivity, because they are not needed anymore. But what if |R_| is axiomatized as an equivalence relation using different axioms? Then we can remove any axiom about |R_| that is implied by reflexivity, symmetry, and transitivity. Luckily we have already computed a table of which properties imply which other ones (shown in Appendix \ref{sec:implications}).

\parag{Pequalification} There are commonly occurring binary relations called {\em partial equivalence relations} that almost behave as equivalence relations, but not quite. In particular, they do not have to obey the axiom of reflexivity. Can we do something for these too?

It turns out that a set with a partial equivalence relation |R_| can be partitioned into two subsets: (1) one subset on which |R_| is an actual equivalence relation, and (2) one subset of elements which are not related to anything, not even themselves.

Thus, an alternative way of dealing with partial equivalence relations |R_| is to create two new symbols, |rep_| and |P|, and replace all occurrences of |R_| with a formula involving |rep_| and |P|:
\begin{code}
R_ symmetric     §  
R_ transitive    -->   §
T[.. R(x,y) ..]  §     T[.. (P(x) && P(y) && rep(x)=rep(y)) ..]
\end{code}
Here, |P| is the predicate that indicates the subset on which |R_| behaves as an equivalence relation.

We call this transformation {\em pequalification}. Doing so may be beneficial because the reasoning now involves built-in equality reasoning instead of reasoning about an unknown symbol using axioms. However, there is also a clear price to pay since the size of the problem grows considerably.

The transformation is correct, meaning that it preserves (non-)satisfiability: ($\Rightarrow$) If we have a model of the LHS theory, then |R_| must be interpreted as a partial equivalence relation. Let |P(x):=R(x,x)|, in other words |P_| is the subset on which |R_| behaves like an equivalence relation. Let |rep_| be the representative function of |R_| on |P_|, in other words we have |(P(x) && P(y)) => (R(x,y) <=> rep(x)=rep(y))|. By the definition of |P_| we then also have |R(x,y) <=> (P(x) && P(y) && rep(x)=rep(y))|. Thus we also have a model of the RHS theory. ($\Leftarrow$) If we have a model of the RHS theory, let |R(x,y):=P(x) && P(y) && rep(x)=rep(y)|. It is clear that |R_| is symmetric, and transitive, and therefore we have model of the LHS theory.

% ------------------------------------------------------------------------------
% - dealing with total orders

\section{Dealing with total orders}

\parag{Orderification} Many reasoning tools have built-in support for arithmetic, in particular they support an ordering |<=| on numbers. Can we ``borrow'' this operator when dealing with general total orders? It turns out we can. Suppose we have a total order
\begin{code}
R_ : A ** A -> Bool
\end{code}
We can now create a new symbol
\begin{code}
rep_ : A -> RR
\end{code}
We then replace all occurrences of |R_| with a formula involving |rep_| in the following way:
\begin{code}
R_ total          §
R_ antisymmetric  -->   §
R_ transitive     §
T[.. R(x,y) ..]   §     T[.. rep(x)<=rep(y) ..]
\end{code}
(Here, |<=| is of course the ordering on reals.) We call this transformation {\em orderification}. Doing so may be beneficial because the reasoning now involves built-in arithmetic reasoning instead of reasoning about an unknown symbol using axioms.

The above transformation is correct, meaning that it preserves (non-)satisfiability: ($\Rightarrow$) If we have a model of the LHS theory, then without loss of generality (by L{\"o}wenheim-Skolem), we can assume that the domain is countable. Also, |R_| must be interpreted as a total order. We now construct |rep_| recursively as a mapping from the model domain to |RR|, such that we have |R(x,y) <=> rep(x)<=rep(y)|, in the following way. Let |{a0, a1, a2, ..}| be the domain of the model, and set |rep(a0):=0|. For any |n>0|, pick a value for |rep(an)| that is consistent with the total order |R_| and all earlier domain elements |ai|, for |0 <= i < n|. This can always be done because there is always extra room for a new element between any two distinct values of |RR|. Thus we also have a model of the RHS theory. ($\Leftarrow$) If we have a model of the RHS theory, let |R(x,y):=rep(x)<=rep(y)|. It is clear that |R_| is total, antisymmetric, and transitive, and therefore we have model of the LHS theory.

\parag{Note on |QQ| vs. |RR|} The proof would have worked for |QQ| as well instead of |RR|. However, reasoning about real arithmetic in tools is often much cheaper than reasoning about rational arithmetic, which is why we chose |RR|. Using integer arithmetic would however not have been correct.

\parag{Note on strict total orders} One may have expected to have a transformation specifically targeted to strict total orders, i.e. something like:
\begin{code}
R_ antisymmetric^~  §          
R_ asymmetric       -->   §
R_ transitive       §
T[.. R(x,y) ..]     §     T[.. rep(x)<rep(y) ..]
\end{code}
However, the transformation for total orders already covers this case! Any strict total order |R_| is also recognized as a total order |~R_|, and orderification already transforms such theories in the correct way. The only difference is that |R(x,y)| is replaced with |~(rep(x)<=rep(y))| instead of |rep(x)<rep(y)|, which is satisfiability-equivalent. (There may be a practical performance difference, which is not something we have investigated.)

\parag{Maxification} Some reasoning tools do not have orders on real arithmetic built-in, but they may have other concepts that are built-in that can be used to express total orders instead. One such concept is handling of associative, commutative (AC) operators.

For such a tool, one alternative way of dealing with total orders |R_| is to create a new symbol |max_| and replace all occurrences of |R_| with a formula involving |max_|:
\begin{code}
R_ total          §     max_ associative
R_ antisymmetric  -->   max_ commutative
R_ transitive     §     forall x,y . max(x,y)=x || max(x,y)=y
T[.. R(x,y) ..]   §     T[.. max(x,y)=y ..]
\end{code}
We call this transformation {\em maxification}. Doing so may be beneficial because the reasoning now involves built-in equality reasoning with AC unification (and one extra axiom) instead of reasoning about an unknown relational symbol (using three axioms).

The above transformation is correct, meaning that it preserves (non-)satisfiability: ($\Rightarrow$) If we have a model of the LHS theory, then |R_| must be interpreted as a total order. Let |max_| be the maximum function associated with this order. CLearly, it must be associative and commutative, and the third axiom also holds. Moreover, we have  |R(x,y) <=> max(x,y)=y|. Thus we also have a model of the RHS theory. ($\Leftarrow$) If we have a model of the RHS theory, let |R(x,y):=max(x,y)=y|. Given the axioms in the RHS theory, |R_| is total, antisymmetric, and transitive, and therefore we have model of the LHS theory.

(It may be the case that maxification can also be used to express orders that are weaker than total orders. At the time of this writing, we have not figured out how to do this.)

% ------------------------------------------------------------------------------
% - transitive reflexive

\section{Dealing with reflexive, transitive relations}

\parag{Transification} The last transformation we present is designed as an alternative treatment for any relation that is reflexive and transitive. It does not make use of any built-in concept in the tool. Instead, it transforms theories with a transitivity axiom into theories without that transitivity axiom. Instead, transitivity is {\em specialized} at each {\em positive occurrence} of the relational symbol.

As such, an alternative way of dealing with reflexive, transitive relations |R_| is to create a new symbol |Q_| and replace all positive occurrences of |R_| with a formula involving |Q_|; the negative occurrences are simply replaced by |~Q_|:
\begin{code}
R_ reflexive        §     Q_ reflexive
R_ transitive       -->   
T[..  R(x,y)   ..   §     T[..  (forall r . Q(r,x) => Q(r,y))  ..
      ~R(x,y)  ..]  §           ~Q(x,y)                        ..]
\end{code}
We call this transformation {\em transification}. Doing so may be beneficial because reasoning about transitivity in a naive way can be very expensive for theorem provers, because from transitivity there are many possible conclusions to draw that trigger each other ``recursively''.

Note that the resulting theory does not blow-up; only clauses with a positive occurrence of |R_| gets one extra literal per occurrence.

What is going on here? We replace any positive occurrence of |R(x,y)| with an implication that says ``for any |r|, if you could reach |x| from |r|, now you can reach |y| too''. Thus, we have specialized the transitivity axiom for every positive occurrence of |R_|.

Note that in the RHS theory, |Q_| does not have to be transitive! Nonetheless, the transformation is correct, meaning that it preserves (non-)satisfiability: ($\Rightarrow$) If we have a model of the LHS theory, then |R_| is reflexive and transitive. Now, set |Q(x,y) := R(x,y)|. |Q_| is obviously reflexive. We have to show that |R(x,y)| implies |forall r . Q(r,x) => Q(r,y)|. This is indeed the case because |R_| is transitive. Thus we also have a model of the RHS theory. ($\Leftarrow$) If we have a model of the RHS theory, then |Q_| is reflexive. Now, set |R(x,y) := forall r . Q(r,x) => Q(r,y)|. |R_| is reflexive (by reflexivity of implication) and transitive (by transitivity of implication). Finally, we have to show that |~Q(x,y)| implies |~R(x,y)|, which is the same as showing that |forall r . Q(r,x) => Q(r,y)| implies |Q(x,y)|, which is true because |Q_| is reflexive. Thus we also have a model of the RHS theory. 

% ------------------------------------------------------------------------------
% - experimental results

%KOEN: what tptp version did you use to generate the lagom stora problems?

\section{Experimental results}
We evaluate the effects of the different axiomatizations using two different resolution based theorem provers, E 1.9 \cite{E} (with the \textit{xAuto} and \textit{tAuto} options) and Vampire 4.0 \cite{Vampire} (with the \textit{casc mode} option), and two SMT-solvers, Z3 4.4.2 \cite{Z3} and CVC4 1.4 \cite{CVC4}. The experiments were performed on a 2xQuad Core Intel Xeon E5620 processor with 24 GB physical memory, running at 2.4 GHz. We use a time limit of 5 minutes on each problem. For Vampire, no time limit is passed directly to the theorem prover but instead the process is terminated once the time limit has passed. This was done to keep solving times more stable, since Vampire uses the time limit to control its search strategies.

We started from a set of 10788 test problems from the TPTP, listed as Unsatisfiable or Theorem (leaving out the very large theories). For each problem, a new theory was generated for each applicable transformation. For most problems, no relation matching any of the given criteria was detected, and thus no new theories were produced for these problems. 

\begin{figure}[t]
\begin{center}
\setlength{\tabcolsep}{5.2pt}
\begin{tabular}{lr||rrr||rrr||rrr||rrr}
  & & \multicolumn{3}{c}{E} & \multicolumn{3}{c}{Vampire}&\multicolumn{3}{c}{Z3} &\multicolumn{3}{c}{CVC4} \\
\hline 
equalification & (429) & 422 & +4  & \underline{-33} & 428 & +0  & -4 & 362 & +50 & \underline{-3} & 370 & +18 & \underline{-39} \\
pequalification & (117) & 96 & +0 & -34 & 87 & +5 & \underline{-8}  & 38 & +9 & \underline{-4} & 59 & +1  &  \underline{-11} \\
transification  & (545) & 324 & {\bf +2} & -26 & 274 & {\bf +32} & \underline{-10} & 234 & +10 & -46 & 255 & +13 & -42 \\
ordification  & (327) & & n/a & & 292 & {\bf +19} & \underline{-29} & 238 & {\bf +41} & \underline{-21} & 267 & {\bf +12} & -29  \\
maxification  & (327) & 273 & +1 & -23 & 292 & +0 & -1 & 238 & +1 & -41 & 267 & +4 & \underline{-0} \\

\end{tabular}
\end{center}
\vspace{-0.5cm}
\caption{Table showing for each theorem prover the number of test problems solved before the transformation,  how many new problems are solved after the transformation, and the number of problems that could be solved before but not after the transformation. (Total number of applicable problems for each transformation in parentheses). A +value in {\bf boldface} indicates that there were hard problems (Rating 1.0) solved with that combination of treatment and theorem prover. An \underline{underlined} -value indicates that time slicing (running both methods in 50\% of the time each) solves strictly more problems with that combination of treatment and theorem prover.}
\label{fig:overview}
\end{figure}

\subsection{Equivalence relations}

Equivalence relations were present in 429 of the test problems. The majority of these problems appear in the GEO and SYN categories. Interestingly, among these 429 problems, there are only 22 problems whose equivalence relations are axiomatized with transitivity axioms. The remaining 407 problems axiomatize equivalence relations with euclidean and reflexivity axioms, as discussed in section \ref{sec:discovery}. The number of equivalence relations in each problem ranges from 1 to 40, where problems with many equivalence relations all come from the SYN category. There is no clear correspondence between the number of equivalence relations in a problem and the performance of the prover prior to and after the transformation. 

\paragraph{Equalification}
As can be seen in Figure \ref{fig:overview}, equalification performs very well with Z3, and somewhat well with CVC4, while it worsens the results of the resolution based provers, which already performed well on the original problems. %TODO : Koen - why may this be? 
Using a time-slicing strategy, which runs the prover on the original problem for half the time and on the transformed problem for the second half, would solve strictly more problems than the original for all of the theorem provers used in the evaluation. Figure \ref{fig:e_equalified} shows in more detail the effect on solving times for the different theorem provers.
%TODO: for the camera ready version we should make the time slicing squares the biggest possible size.

\begin{figure}[t]
\includegraphics[scale=0.65,trim=10mm 00mm 20mm 0mm]{Plots/Equalified/E/test_original_e_equalified_e_300.eps}
%\includegraphics[scale=0.22]{Plots/Equalified/E/}
%\begin{figure}[t]
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/Equalified/Vampire/test_original_vampire_equalified_vampire_300.eps}\\
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/Equalified/Z3/test_original_z3_equalified_z3_300.eps}
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/Equalified/CVC4/test_original_cvc4_equalified_cvc4_300.eps}
\caption{The time taken to solve problems, with and without equalification, using E, Vampire, Z3 and CVC4 }
%\includegraphics[scale=0.22]{Plots/Equalified/E/}
%\end{figure}
\label{fig:e_equalified}
\end{figure}

%TODO KOEN: i don't like the word treatment. it sounds like a cream you put on your skin.

\paragraph{Pequalification}

In 117 of the test problems, relations that are transitive and symmetric, but not reflexive, were found. The majority of these problems are in the CAT and FLD categories of TPTP. All of the tested theorem provers perform worse on these problems compared to the problems with true equivalence relations. This is also the case after performing pequalification. Pequalification turns out to be particularly bad for E, which solves 34 fewer problems after the transformation. Pequalification makes Z3 perform only slightly better and Vampire and CVC4 slightly worse. 
When the differences to the performance is small, it is hard to know if the effect is due to the new axiomatisation, or to other reasons. For example, we have observed that simply shuffling the axioms of a theory can cause the results to deviate in a similar way. 
%TODO Koen can we say anything more here?

\subsection{Total orderings}
Total orders were found in 327 problems. The majority are in the SWV category, and the remaining in HWV, LDA and NUM.  In 77 of the problems, the total order is positively axiomatised, and in the other 250 problems it is negative (and thus axiomatised as a strict total order). There is never more than one order present in any of the problems. 

\paragraph{Ordification}
For each of the problems, we ran the theorem provers with built-in support for arithmetic on the problems before and after applying ordification. Vampire was run on a version in TFF format \cite{TFF}, and Z3 and CVC4 on a version in SMT format \cite{SMT}. The original problems were also transformed into TFF and SMT in order to achieve a relevant comparison. Ordification performs well for Z3, while for Vampire and CVC4 it is good for some problems and bad for some. Figure \ref{fig:ordified} shows how solving times are affected, and the diagrams also show great potential for time slicing, in particular for Vampire and Z3.
\paragraph{Hard problems solved using Ordification}
After Ordification, 15 problems, all from the SWV category, with rating 1.0 are solved. (SWV004-1, SWV035+1, SWV040+1, SWV044+1 , SWV049+1, SWV079+1, SWV100+1, SWV101+1, SWV108+1, SWV110+1, SWV113+1, SWV118+1, SWV120+1, SWV124+1, SWV130+1) Vampire and Z3 each solve 14 hard problems and CVC4 solves 13 of them. Rating 1.0 means that no known current theorem prover solves the problem. One problem (SWV004-1) is even categorized as Unknown, which means that no prover has ever solved it.

\begin{figure}[t]
%\includegraphics[scale=0.40,trim=20mm 00mm 30mm 0mm]{Plots/Ordified/E/test_original_e_ordified_e_300.eps}
%\includegraphics[scale=0.22]{Plots/Equalified/E/}
%\begin{figure}[t]
\includegraphics[scale=0.55,trim=20mm 0mm 30mm 0mm]{Plots/Ordified/Vampire/test_original_vampire_ordified_vampire_300.eps}
\includegraphics[scale=0.55,trim=7mm 0mm 30mm 0mm]{Plots/Ordified/Z3/test_original_Z3_ordified_Z3_300.eps}
\includegraphics[scale=0.55,trim=7mm 0mm 40mm 0mm]{Plots/Ordified/CVC4/test_original_CVC4_ordified_cvc4_300.eps}
\caption{Effects of ordification, using Vampire, Z3 and CVC4 }
%\includegraphics[scale=0.22]{Plots/Equalified/E/}
%\end{figure}
\label{fig:ordified}
\end{figure}
\paragraph{Maxification}
Maxification, the second possible treatment of total orders, turned out to be disadvantageous to E and Z3, while having very little effect on Vampire and CVC4 (see figure \ref{fig:overview}).
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
545 test problems include relations that are transitive and reflexive, excluding equivalence relations and total orders. In all of them, transitivity occurs syntactically as an axiom. The problems come from a variety of categories, but a vast majority are in SET, SEU and SWV.  Only about half of the original problems were solved by each theorem prover, which may indicate that transitivity axioms are difficult for current theorem provers to deal with.  We evaluate the performance of the theorem provers before and after transification. Problems that include equivalence relations and total orders are excluded, as the corresponding methods equalification and ordification give better results and should be preferred. Vampire benefits the most from transification, and solves 32 new problems after the transformation, while 10 previously solvable problems become unsolvable within the time limit. For E, the effect of transification is almost exclusively negative.
%TODO what to write here?? 
Vampire also has a significantly worse performance than E overall on the original problems that include relations that are transitive and reflexive.
Both Z3 and CVC4 perform worse after the transformation, but time-slicing can be a good way to improve the results. 

%TODO KOEN: who uses chaining? is Vampire better on transified problems because it doesn't use chaining?

\begin{figure}[t]
\includegraphics[scale=0.65,trim=10mm 00mm 20mm 0mm]{Plots/OnlyTransify/E/test_original_e_transified_e_300.eps}
%\includegraphics[scale=0.22]{Plots/Equalified/E/}
%\begin{figure}[t]
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/OnlyTransify/Vampire/test_original_vampire_transified_vampire_300.eps}\\
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/OnlyTransify/Z3/test_original_z3_transified_z3_300.eps} 
\includegraphics[scale=0.65,trim=10mm 0mm 20mm 0mm]{Plots/OnlyTransify/CVC4/test_original_cvc4_transified_cvc4_300.eps}
\caption{Effects of transification, using E, Vampire, Z3 and CVC4 }
%\includegraphics[scale=0.22]{Plots/Equalified/E/}
%\end{figure}
\end{figure}


\paragraph{Hard problems solved using Transification}
After transification, three new problems with rating 1.0 are solved. Two by Vampire (SEU322+2 and SEU372+2) and one by E (ROB025-1).

\paragraph{Equalification and Transification}
Since all equivalence relations are transitive and reflexive, the method for transification works also on equivalence relations. Comparing the two methods on the 429 problems with equivalence relations, we concluded that equalification and transification work equally bad for E, Vampire and CVC4. Both transification and equalification improve the results for Z3, but equalification does so significantly. 

\paragraph{Ordification and Transification}
We compared ordification and transification on the 327 problems containing total orders. Transification seems to make these problems generally more difficult for theorem provers to solve, while ordification instead improved the results on many of the problems.  Transification makes the theorem prover perform worse on these problems also for E, which cannot make use of ordification since it does not provide support for arithmetic.

%(equalification: win 50 lose 3, transification: win 46, lose 27)

% ------------------------------------------------------------------------------
% - discussion and related work
% - conclusions and future work

\section{Discussion, Conclusions, and Future Work}

Chaining \cite{bachmair1998ordered} is a family of methods that limit the use of transitivity-like axioms in proofs by only allowing chains of them to occur in proofs. The result is a complete proof system that avoids the derivation of unnecessary consequences of transitivity. However, chaining is not implemented in any of the reasoning tools we considered for this paper.

We have developed 5 transformations that treat common transformation binary relations in alternative ways, namely equalification (for equivalence relations), pequalification (for partial equivalence relations), ordification and maxification (for total orders), and transification (for reflexive, transitive relations). 

Each of these methods (except for perhaps pequalification) seems to be beneficial for use in certain practical situations for certain automated reasoning tools.

We have also developing a method for syntactically discovering the presence of these relations in a given theory.

Future work:

Investigate difference between ordification and stordification

More binary relations (not only transitive ones).

Investigating what happens for satisfiable problems. This is hard because there are not so many satisfiable problems that have these kinds of relations. However, we can measure the time it takes to show that there doesn't exist a model of size N, for a fixed N.

Generalizing maxification to other orders than total orders.

Suggesting ways of adding these techniques to provers so that they become built-in. Other ways of primitively supporting these in provers.

% ------------------------------------------------------------------------------
% - references

\bibliographystyle{plain}
\bibliography{main}

% ------------------------------------------------------------------------------
% - appendix

\appendix
\section{Implications between properties} \label{sec:implications}
Here follows the complete list of implications between properties that we discovered using the method described in Sect. \ref{sec:discovery}.

{\footnotesize
%{
%format <= = "\Leftarrow"
%include Implications/implications2.tex
%}
}

\end{document}

