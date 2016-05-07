\documentclass{easychair}
\usepackage{amssymb}
\usepackage{mathabx}
\usepackage{subcaption}
%include polycode.fmt

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
%format -->    = "\;\;\rightarrowtriangle\;\;"

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

Most automated reasoning tools for first-order logic have some kind of built-in support for reasoning about equality. Why? Because equality is an extremely common binary relation, and there are great performance benefits from providing built-in support for equality. Together, these two advantages by far outweigh the cost of implementation.

Other common concepts for which there exists built-in support in many tools are associative, commutative operators; and real-valued, rational-valued, and integer-valued arithmetic. Again, these concepts seem to appear often enough to warrant the extra cost of implementing special support in reasoning tools.

This paper is concerned with investigating what kind of special treatment we could give to commonly appearing transitive binary relations, and what effect this treatment has in practice. For now, we are mainly looking at (1) what a user of a reasoning tool may do herself to optimize the treatment of these binary relations, and (2) how a preprocessing tool may be able to do this automatically. Adding built-in reasoning support in the tools themselves is not a main concern of this paper.

By ``treatment'' we mean any way of logically expressing the relation. For example, a possible treatment of a binary relation |R_| in a theory |T| may simply mean axiomatizing |R_| in |T|. But it may also mean transforming |T| into a satisfiability-equivalent theory |T'| where |R_| does not even syntactically appear.

As an example, consider a theory |T| in which an equivalence relation |R_| occurs. One way to deal with |R_| is to simply axiomatize it, by means of reflexivity, symmetry, and transitivity:
\begin{code}
(forall x . R(x,x)) && (forall x,y . R(x,y) => R(y,x)) && (forall x,y,z . R(x,y) && R(y,z) => R(x,z))
\end{code}
Another way is to ``borrow'' the built-in equality treatment that exists in most theorem provers. We can do this by introducing a new symbol |rep_|, and replacing all occurrences of |R_| by a formula:
\begin{code}
R(x,y)  -->  rep(x)=rep(y)
\end{code}
(The intuition here is that |rep_| is now the representative function of the relation |R_|.) No axioms are needed. As we shall see, this alternative treatment of equivalence relations is satisfiability-equivalent with the original one, and actually is beneficial in practice in certain cases.

In general, we strive to make use of concepts already built-in to the reasoning tool in order to express other concepts that are not built-in.

For the purpose of this paper, we have decided to concentrate on three different kinds of relations: (1) {\em equivalence relations} and {\em partial equivalence relations}, (2) {\em total orders} and {\em strict total orders}, and (3) {\em reflexive, transitive relations}. The reason we decided to concentrate on these three are because (a) they appear frequently in practice, and (b) we found well-known ways but also novel ways of dealing with these.

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
784  & asymmetric / total \\
388  & symmetric \\
3    & coreflexive \\
(163 & other)
\end{tabular}
\end{center}
\vspace{-0.5cm}
\caption{Number of occurrences of binary relation properties in TPTP}
\label{fig:occurs}
\end{figure}

When we investigated the number of occurrences of these properties in an older version of the TPTP problem library \cite{tptp}, we ended up with the table in Fig.\ \ref{fig:occurs}. The table was constructed by gathering all clauses from all TPTP problems (after clausification), and keeping every clause that only contained a binary relation symbol and, possibly, equality. Each such clause was then categorized as an expression of a basic property of a binary relation symbol. We found only 163 such clauses that did not fit any of the 8 properties we chose as basic properties. These were all quite esoteric and did not seem to have a standard name in mathematics.

The table also contains occurrences where a {\em negated relation} was stated to have a certain property, and also occurrences where a {\em flipped relation} (a relation with its arguments swapped) was stated to have a certain property, and even occurrences of combined negated and flipped relations. This explains for example why the number of occurrences of total relations is the same as for asymmetric relations; if a relation is total, its negated relation is asymmetric and vice-versa.

We adopt the following notation. Given a property of binary relations |prop|, we define its {\em negated version}, which is denoted by |prop^~|. The property |prop^~| holds for |R_| if and only |prop| holds for |~R_|. Similarly, we define the {\em flipped version} of a property |prop|, which is denoted by |prop^^|. The property |prop^^| holds for |R_| if and only |prop| holds for the flipped version of |R_|. Using this notation, we can for example say that |total| is equivalent with |asymmetric^~|. Sometimes the property we call |euclidean| here is called |right euclidean|; the corresponding variant |left euclidean| can be denoted |euclidean^^|.

Using this notation on the 8 original basic properties from Fig.\ \ref{fig:props}, we end up with 32 new basic properties that we can use. However, as we have already seen, some of these are equivalent to each other.

This paper will look at 5 kinds of different relations, which can be defined as combinations of basic properties:
\begin{code}
equivalence relation            ==  {reflexive, symmetric, transitive}
partial equivalence relation    ==  {symmetric, transitive}
total order                     ==  {total, antisymmetric, transitive}
strict total order              ==  {antisymmetric^~, asymmetric, transitive}
reflexive, transitive relation  ==  {reflexive, transitive}
\end{code}
As a side note, in mathematics, strict total orders are sometimes defined using a property called {\em trichotomous}, which means that exactly one of |R(x,y)|, |x=y|, or |R(y,x)| must be true. However, when you clausify this property in the presence of transitivity, you end up with |antisymmetric^~| which says that at least one of |R(x,y)|, |x=y|, or |R(y,x)| must be true. There seems to be no standard name in mathematics for the property |antisymmetric^~|, which is why we use this name.

\begin{figure}[t]
\begin{center}
\begin{tabular}{rl}
429+19 & equivalence relations \\
117+72 & partial equivalence relations (excluding true equivalence relations) \\
327+8 & total orders / strict total orders \\
872+4 & reflexive and transitive relations (excluding equivalence relations)\\
\end{tabular}
\end{center}
\vspace{-0.5cm}
\caption{Number of occurrences of common combinations of basic binary relation properties in TPTP}
\label{fig:occurs2}
\end{figure}

% ------------------------------------------------------------------------------
% - discovering relations

\section{Syntactic discovery of binary relations} \label{sec:discovery}

If our goal is to automatically choose the right treatment of equivalence relations, total orders, etc., we must have an automatic way of identifying them in a given theory. It is easy to discover for example an equivalence relation in a theory by means of syntactic inspection. If we find the presence of the axioms |reflexive|, |symmetric|, and |transitive|, for the same relational symbol |R_|, we know that |R_| is a binary relation.

But there is a problem. There are other ways of axiomatizing equivalence relations. For example, a much more common way to axiomatize equivalence relations in the TPTP is to state the two properties |reflexive| and |euclidean| for |R_|\footnote{A possible reason for this is a paper written in the 1990s that argued for this alternative axiomatization. The first author of this paper has at one point seen this paper, but at the time of the writing, we have not been able to find it again! If any reviewer knows which paper we are talking about, help would be appreciated.}. 

Rather than by hand enumerating all possible ways to axiomatize certain relations, we wrote a program that computes all possible ways for any combination of basic properties to imply any other combination of basic properties. Our program generates a table (shown in Appendix \ref{sec:implications}) that can be precomputed in a minute or so and used to very quickly detect any alternative axiomatization of binary relations using basic properties.

\begin{figure}[t]
\begin{center}
%include Implications/equivalences.tex
\end{center}
\vspace{-0.5cm}
\caption{Basic properties that are equivalent}
\label{fig:equivs}
\end{figure}

Let's explain how this table was generated. We start with a list of 32 basic properties (the 8 original basic properties, plus their negated, flipped, and negated flipped versions). Firstly, we use an automated theorem prover (we used E \cite{eprover}) to discover which of these are equivalent with other such properties. The result is displayed in Fig.\ \ref{fig:equivs}. Thus, 17 basic properties can be removed from the list, because they can be expressed using other properties. The list of basic properties now has 15 elements left.

Secondly, we want to generate all implications of the form |{prop1, .., propn} => prop| where the set |{prop1, .., propn}| is minimal (as displayed in Appendix \ref{sec:implications}). We do this separately for each |prop|.

The procedure uses a simple constraint solver (SAT-solver) to keep track of all implications it has tried so far, and consists of one main loop. At every loop iteration, the constraint solver guesses a set |{prop1, .., propn}| from the set of all properties |P-{prop}|. The procedure then asks E whether or not |{prop1, .., propn} => prop| is valid. If it is, then we look at the proof that E produces, and print the implication |{propa, .., propb} => prop|, where |{propa, .., propb}| is the subset of properties that were used in the proof. We then also tell the constraint solver never to guess a superset of |{propa, .., propb}| again. If the guessed implication can not be proven, we tell the constraint solver to never guess a subset of |{prop1, .., propn}| again. The procedure stops when no guesses that satisfy all constraints can be made anymore.

After the loop terminates, we may need to clean up the implications somewhat because some implications may subsume others.

In order to avoid generating inconsistent sets |{prop1, .., propn}| (that would imply any other property), we also add the artificial inconsistent property |false| to the set, and generate implications for this property first. We exclude any found implication here from the implication sets of the real properties. 

This procedure generates a complete list of minimal implications. It works well in practice, especially if all guesses are maximized according to their size.

To detect a binary relation |R_| with certain properties in a given theory, we simply gather all basic properties about |R_| that occur in the theory, and compute which other properties they imply, using the pre-generated table. In this way, we never have to do any theorem proving in order to detect a binary relation with certain properties.

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
To explain the above notation: We have two theories, one on the left-hand side of the arrow, and one on the right-hand side of the arrow. The transformation transforms any theory that looks like the left-hand side into a theory that looks like the right-hand side. We write |T[.. e ..]| for theories in which |e| occurs syntactally.

We call this transformation {\em equalification}. Doing so may be beneficial because the reasoning now involves built-in equality reasoning instead of reasoning about an unknown symbol using axioms.

The above transformation is correct, meaning that it preserves (non-)satisfiability: ($\Rightarrow$) If we have a model of the LHS theory, then |R_| must be interpreted as an equivalence relation. Let |rep_| be the representative function of |R_|, in other words we have |R(x,y) <=> rep(x)=rep(y)|. Thus we also have a model of the RHS theory. ($\Leftarrow$) If we have a model of the RHS theory, let |R(x,y):=rep(x)=rep(y)|. It is clear that |R_| is reflexive, symmetric, and transitive, and therefore we have model of the LHS theory.

In the transformation, we also remove the axioms for reflexivity, symmetry, and transitivity, because they are not needed anymore. But what if |R_| is axiomatized as an equivalence relation using different axioms? Then we can remove any axiom about |R_| that is implied by reflexivity, symmetry, and transitivity. Luckily we have already computed a table of which properties imply which other ones (in Appendix \ref{sec:implications}).

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

% ------------------------------------------------------------------------------
% - dealing with total orders

\section{Dealing with total orders}

\parag{Orderification} Many reasoning tools have built-in support for arithmetic, in particular |<=|. Can we ``borrow'' this operator when dealing with general total orders? It turns out we can. Suppose we have a total order
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

\parag{Note on |QQ| vs. |RR|} The proof would have worked for |QQ| as well instead of |RR|. However, reasoning about real arithmetic in 
tools is often much cheaper than reasoning about rational arithmetic, which is why we chose |RR|. Integer arithmetic would not have been correct.

\parag{Note on strict total orders} One may have expected to have a transformation specifically targeted to strict total orders, i.e. something like:
\begin{code}
R_ antisymmetric^~  §          
R_ asymmetric       -->   §
R_ transitive       §
T[.. R(x,y) ..]     §     T[.. rep(x)<rep(y) ..]
\end{code}
However, the transformation for total orders already covers this case! Any strict total order |R_| is recognized as a total order |~R_|, and orderification already transforms such theories in the correct way. The only difference is that |R(x,y)| is replaced with |~(rep(x)<=rep(y))| instead of |rep(x)<rep(y)|, which is satisfiability-equivalent.

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

\parag{Transification} The last transformation we present is designed as an alternative treatment for any relation that is reflexive and transitive. It does not make use of any built-in concept in the tool. Instead, it transforms theories with a transitivity axiom into theories without that transitivity axiom. Instead, transitivity is {\em specialized} at each positive occurrence of the relational symbol.

As such, an alternative way of dealing with reflexive, transitive relations |R_| is to create a new symbol |Q_| and replace all positive occurrences of |R_| with a formula involving |Q_|; the negative occurrences are simply replaced by |Q_|:
\begin{code}
R_ reflexive        §     Q_ reflexive
R_ transitive       -->   
T[..  R(x,y)   ..   §     T[..  (forall r . Q(r,x) => Q(r,y))  ..
      ~R(x,y)  ..]  §           ~Q(x,y)                        ..]
\end{code}
We call this transformation {\em transification}. Doing so may be beneficial because reasoning about transitivity in a naive way can be very expensive for theorem provers, because there are many possible conclusions to draw that trigger each other ``recursively''.

Note that the resulting theory does not blow-up; every clause with a positive occurrence of |R_| gets one extra literal per occurrence.

What is going on here? We replace any positive occurrence of |R(x,y)| with an implication that says ``for any |r|, if you could reach |x| from |r|, now you can reach |y| too''. Thus, we have specialized the transitivily axiom for every positive occurrence of |R_|.

Note that in the RHS theory, |Q_| does not have to be transitive! Nonetheless, the transformation is correct, meaning that it preserves (non-)satisfiability: ($\Rightarrow$) If we have a model of the LHS theory, then |R_| is reflexive and transitive. Now, set |Q(x,y) := R(x,y)|. |Q_| is obviously reflexive. We have to show that |R(x,y)| implies |forall r . Q(r,x) => Q(r,y)|. This is indeed the case because |R_| is transitive. Thus we also have a model of the RHS theory. ($\Leftarrow$) If we have a model of the RHS theory, then |Q_| is reflexive. Now, set |R(x,y) := forall r . Q(r,x) => Q(r,y)|. |R_| is reflexive (by reflexivity of implication) and transitive (by transitivity of implication). Finally, we have to show that |~Q(x,y)| implies |~R(x,y)|, which is the same as showing that |forall r . Q(r,x) => Q(r,y)| implies |Q(x,y)|, which is true because |Q_| is reflexive. Thus we also have a model of the RHS theory. 

% ------------------------------------------------------------------------------
% - experimental results

\section{Experimental results}
We evaluate the effects of the different axiomatizations using four different theorem provers: E, Vampire, Z3 and CVC4. 
(TODO: Why did we choose them?) We use a timeout of 5 minutes on each problem. (For Vampire, no timeout is set, but the prover is simply interrupted after 5 minutes if it has not yet terminated.)

\subsection{Equivalence relations}

We detected 429 problems with equivalence relations among the TPTP problems listed as Unsatisfiable and Theorem. The majority of problems appear in the GEO and SYN categories.

Interestingly, among these 429 problems, there are only 22 problems whose equivalence relations are axiomatized with transitivity axioms. The remaining 407 problems axiomatize equivalence relations with euclidean and reflexivity axioms. The number of equivalence relations in each problem ranges from 1 to 40, where problems with many equivalence relations all come from the SYN category. 

In our evaluations, there is no clear correspondence between the number of equivalence relations in a problem and the performance of the prover prior to and after the transformation. The initial axiomatisation of the equivalence relation (transitive or euclidean) does not have any notable effect either.
TODO check if this is the case also for Z3.

\paragraph{Original vs. Equalified for E}
E manages to solve 4 problems that it did not solve before the transformation. At the same time, it times out on 33 problems that it was previously able to solve.
\begin{figure}[t]
\includegraphics[scale=0.70,trim=10mm 00mm 20mm 0mm]{Plots/Equalified/E/test_original_e_equalified_e_300.eps}
%\includegraphics[scale=0.22]{Plots/Equalified/E/}
%\begin{figure}[t]
\includegraphics[scale=0.70,trim=10mm 0mm 20mm 0mm]{Plots/Equalified/Vampire/test_original_vampire_equalified_vampire_300.eps}\\
\includegraphics[scale=0.70,trim=10mm 0mm 20mm 0mm]{Plots/Equalified/Z3/test_original_z3_equalified_z3_300.eps}
\includegraphics[scale=0.70,trim=10mm 0mm 20mm 0mm]{Plots/Equalified/CVC4/test_original_cvc4_equalified_cvc4_300.eps}
\caption{Effects of equalification, using E, Vampire, Z3 and CVC4 }
%\includegraphics[scale=0.22]{Plots/Equalified/E/}
%\end{figure}
\end{figure}

\paragraph{Original vs. Equalified for Vampire}
4 problems that were easily solved by Vampire become unsolvable after the transformation.

\paragraph{Original vs. Equalified for Z3}
For Z3, the effect is reversed.  Z3 solves 50 new problems after the transformation, while it times out on 3 problems that it previously solved.

\paragraph{Original vs. Equalified for CVC4}
With CVC4, 18 new problems are solved after the transformation, while 39 problems become unsolvable.

%original vs. equalified for Paradox - Satisfiable and Unsatisfiable



Conclusion: "Equalification" is generally bad for E and Vampire, gives mixed results for CVC4 and works very well for Z3.

Partial equalification seems to have a negative effect for all the provers used in our evaluation. While it does allow three of the provers to solve a few additional problems, this could be due to reasons unrelated to the axiomatisation of the partial equivalence relation. Simply shuffling the axioms of a theory can sometimes have the effect of a problem becoming solvable or unsolvable. We did an experiment where we shuffled the axioms of 11646 TPTP problems. After randomly shuffling the axioms, 72 problems became unsolvable, while 71 problems became solvable, using E with a timeout of 1 minute.

\subsection{Transitive and Reflexive relations}

We present here the results of transification on problems with transitive and reflexive relations excluding equivalence relations and total orders. For equivalence relations and total orders the corresponding methods equalification and ordification work better and should be used exclusively.

\begin{figure}[t]
\includegraphics[scale=0.70,trim=10mm 00mm 20mm 0mm]{Plots/OnlyTransify/E/test_original_e_transified_e_300.eps}
%\includegraphics[scale=0.22]{Plots/Equalified/E/}
%\begin{figure}[t]
\includegraphics[scale=0.70,trim=10mm 0mm 20mm 0mm]{Plots/OnlyTransify/Vampire/test_original_vampire_transified_vampire_300.eps}\\
\includegraphics[scale=0.70,trim=10mm 0mm 20mm 0mm]{Plots/OnlyTransify/Z3/test_original_z3_transified_z3_300.eps} 
\includegraphics[scale=0.70,trim=10mm 0mm 20mm 0mm]{Plots/OnlyTransify/CVC4/test_original_cvc4_transified_cvc4_300.eps}
\caption{Effects of transification, using E, Vampire, Z3 and CVC4 }
%\includegraphics[scale=0.22]{Plots/Equalified/E/}
%\end{figure}
\end{figure}


\paragraph{Original vs. Transified for E}
Win 2, lose 26
% on eqrels: lose 5 win 5
%good for 4, bad for 60
\paragraph{Original vs. Transified for Vampire}
Win 32, lose 10.
% on eqrels: lose 9 win 0. compared to equalification: win 2, lose 7.
%good for 32, bad for 20 

\paragraph{Original vs. Transified for Z3}
Win 10, lose 46
%on eqrels: win 46 lose 27) comparing to equalification, it wins 4 and loses 32.
%on tos + trans: good for 10  bad for 121

\paragraph{Original vs. Transified for CVC4}
Win 13, lose 42
%good for 14, bad for 103

\subsection{Equalification and Transification}
Since all equivalence relations are transitive and reflexive, the method for transification works also on equivalence relations. Comparing the two methods on the 429 problems with equivalence relations, we concluded that equalification and transification work equally bad for E, Vampire and CVC4. Both transification and equalification improves the results for Z3, but equalification does so significantly. (equalification: win 50 lose 3, transification: win 46, lose 27)


\subsection{Total orderings}

\begin{figure}[t]
%\includegraphics[scale=0.40,trim=20mm 00mm 30mm 0mm]{Plots/Ordified/E/test_original_e_ordified_e_300.eps}
%\includegraphics[scale=0.22]{Plots/Equalified/E/}
%\begin{figure}[t]
\includegraphics[scale=0.40,trim=5mm 0mm 30mm 0mm]{Plots/Ordified/Vampire/test_original_vampire_ordified_vampire_300.eps}
\includegraphics[scale=0.40,trim=5mm 0mm 30mm 0mm]{Plots/Ordified/Z3/test_original_Z3_ordified_Z3_300.eps}
\includegraphics[scale=0.40,trim=5mm 0mm 40mm 0mm]{Plots/Ordified/CVC4/test_original_CVC4_ordified_cvc4_300.eps}
\caption{Effects of ordification, using Vampire, Z3 and CVC4 }
%\includegraphics[scale=0.22]{Plots/Equalified/E/}
%\end{figure}
\end{figure}

\paragraph{Total ordering vs. strict total ordering for E}

\paragraph{Total ordering vs. strict total ordering for Vampire}

(total ordering/neg vs. strict total ordering/neg for E, Vampire

or some other comparisons)

total ordering vs. $\leq_\mathbb{R}$ for Z3
solves 41 new problems, times out on 21

total ordering vs. $\leq_\mathbb{R}$ for CVC4
solves 12 new, times out on 29

total ordering vs. $\leq_\mathbb{R}$ for Vampire
solves 13 new problems, times out on 34 new problems.

(Should we show

strict-total ordering vs. $\leq_\mathbb{R}$ for Z3

strict-total ordering vs. $\leq_\mathbb{R}$ for CVC4


separately? Only if the results differ.)

\subsection{Maxification}

(( ANN: How many rating 1 problems can be proven now? ))

% ------------------------------------------------------------------------------
% - discussion and related work

\section{Discussion and Related Work}

chaining \cite{bachmair1998ordered}

...

% ------------------------------------------------------------------------------
% - conclusions and future work

\section{Conclusions and Future Work}

...

Future work:

Investigating what happens for satisfiable problems.

Generalizing maxification to other orders than total orders.

% ------------------------------------------------------------------------------
% - references

\bibliographystyle{plain}
\bibliography{main}

% ------------------------------------------------------------------------------
% - appendix

\appendix
\section{Implications between properties} \label{sec:implications}
Here follows the complete list of implications between properties that we discovered using the method described in Sect. \ref{sec:discovery}.

{\small
%{
%format <= = "\Leftarrow"
%include Implications/implications.tex
%}
}

\end{document}

