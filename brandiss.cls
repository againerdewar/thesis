%  ************************** BRANDISS.CLS **************************
%  Brandeis LaTeX2e dissertation class.  Set up according to the rules
%  outlined by the GSAS for acceptable dissertation format.  Be sure to
%  check that the output matches the current specifications.  The
%  formatting requirements are on-line at:
%     http://www.brandeis.edu/gsas/students
%  under ``Dissertation Guidelines.''

%  This class was written using the guidelines in the ``LaTeX2e for
%  class and package writers'' document available on-line at:
%     http://www.math.smith.edu/Local/latexdocs/html/clsguide/clsguide.html

%  This class is derived from one written by Mario Bourgoin.
%  It was extended in 2011 by Andrew Gainer.

\NeedsTeXFormat{LaTeX2e}[1994/06/01]
\ProvidesClass{brandiss}[2011/05/01 v1.1 Local LaTeX class]

\RequirePackage{etoolbox}

%**************************** Class Options  ************************

%  uncompressed|compressed -> compressed or uncompressed [default] PDF.
%  The uncompressed|compressed option is only meaningful when a PDF is
%  being produced.  If ``uncompressed'' is true, the PDF compression
%  level is set to 0 just before document production begins.  And so
%  ``compressed'' really means ``not uncompressed''.
\providetoggle{uncompressed}
\DeclareOption{uncompressed}{\toggletrue{uncompressed}}
\DeclareOption{compressed}{\togglefalse{uncompressed}}

% sectionbreak|sectionflow -> break pages after sections or don't
% If ''sectionbreak'' is true, add a \clearpage at the end of each section
\providetoggle{sectionbreak}
\DeclareOption{sectionbreak}{\toggletrue{sectionbreak}}
\DeclareOption{sectionflow}{\togglefalse{sectionbreak}}

% singlespace|doublespace -> set spacing in relevant places
\providetoggle{doublespace}
\DeclareOption{singlespace}{\togglefalse{doublespace}}
\DeclareOption{doublespace}{\toggletrue{doublespace}}

% boldmathhdr|normalmathhdr -> use bold math fonts in headers or don't
\providetoggle{boldmathhdr}
\DeclareOption{boldmathhdr}{\toggletrue{boldmathhdr}}
\DeclareOption{normalmathhdr}{\togglefalse{boldmathhdr}}

%  online|printed -> online or printed submission
%  Pass these options to the brandiss package.
\DeclareOption{online}{\PassOptionsToPackage{\CurrentOption}{brandiss}}
\DeclareOption{printed}{\PassOptionsToPackage{\CurrentOption}{brandiss} \ExecuteOptions{submission}}

%  distribution|submission -> distribution or submission version
\DeclareOption{distribution}{\PassOptionsToPackage{\CurrentOption}{brandiss} \ExecuteOptions{sectionflow,singlespace} \PassOptionsToClass{twoside}{amsbook}}  %Distribution default options
\DeclareOption{submission}{\PassOptionsToPackage{\CurrentOption}{brandiss} \ExecuteOptions{sectionbreak,doublespace} \PassOptionsToClass{oneside}{amsbook}} %Submission default options

%  Default Option: Pass all other options to the amsbook class.
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{amsbook}}

%  Default Setup:
\ExecuteOptions{uncompressed,boldmathhdr} % Universal default options

% Default per GSAS formatting requirements
\PassOptionsToClass{12pt}{amsbook}

% Process the options.
\ProcessOptions\relax

%********************** Class and Package Loads  *****************

% The amsbook class provides the main document style.
\LoadClass{amsbook}

% Package brandiss provides front page commands.
\RequirePackage{brandiss}[2004/05/05 v1.0 Local LaTeX package]

% Package ifpdf provides the \ifpdf command.
\RequirePackage{ifpdf}

% Package setspace provides line spacing command.
\RequirePackage{setspace}

% Package geometry sets the margins.  
% REQUIRED: Load before package fancyhdr.
\RequirePackage{geometry}

% Package fancyhdr allows us to set headers and footers.
\RequirePackage{fancyhdr}

%*********************** Settings and Definitions  ******************

% GSAS formatting requirements: If a PDF document is produced, it
% should not be compressed.
\ifpdf\iftoggle{uncompressed}{\AtBeginDocument{\pdfcompresslevel=0}}{}\fi

% GSAS formatting requirements: The left margin is a minimum of 1.5in.
% The top, bottom, and right margins are a minimum of 1in, except top
% margin of a chapter page is a minimum of 2in.  All printed matter
% fits in these margins.  We set the margings at the GSAS minimum.
% The margins of the first page of a chapter come from the amsbook
% format.
\geometry{
  margin=1in, inner=1.5in, %% The margins
  includeheadfoot,%% Header and footer within the margins.
  headheight=3ex,%% Make the headers larger than text and
  headsep=5ex%% separate them from the main text.
}

% GSAS formatting requirements: The page number is consistently placed
% on every page except for the title, signature, and copyright pages.
% It may be centered at the bottom of every page.  We use the fancy
% page style for the main body of the document.  Since the plain style
% used for the front pages, back pages, and the first page of a
% chapter has the page number centered in the footer, we use that
% style for all pages by the least effort principle.
\pagestyle{fancy}
\renewcommand{\headrulewidth}{0.25pt} %% Thin header line.
\fancyhf{}                            %% Clear all fields.
\fancyfoot[C]{\tiny\thepage}          %% Centered page number in the footer.
\if@twoside
  \fancyhead[LE]{\small\leftmark}     %% Chapter name in the left header.
  \fancyhead[RO]{\small\rightmark}    %% Section name in the right header.
\else
  \fancyhead[L]{\small\leftmark}      %% Chapter name in the left header.
\fi

% GSAS formatting requirements: Double line spacing for the front and
% main parts of the document, and the front pages have roman
% numbering.  The \frontmatter command sets double line spacing for
% the whole document.  It also sets roman page numbering and plain
% page style for the pages at the front of the dissertation.
\renewcommand{\frontmatter}{%
  \iftoggle{doublespace}{\doublespacing}{}
  \cleardoublepage
  \pagenumbering{roman}
  \pagestyle{plain}
}

% GSAS formatting requirements: The main and back pages have arabic
% numbering.  The \mainmatter command sets arabic page numbering and
% fancy page style for the pages in the main part of the dissertation.
\renewcommand{\mainmatter}{%
  \cleardoublepage
  \pagenumbering{arabic}
  \pagestyle{fancy}
}

% The \backmatter command sets plain page style for the pages at the
% back of the dissertation (bibliography, index).
\renewcommand{\backmatter}{%
  \singlespacing
  \if@openright\cleardoublepage\else\clearpage\fi
  \let\chaptername\relax % Added so \appendix doesn't affect back matter (see amsbook.cls)
  \pagestyle{plain}
}

% We redefine all the section headings but preserve almost everything from AMS-Book.
% This is clearly not the optimal way to approach the problem of bold mathematics in section headers,
% but AMS-Book does *not* like to work with helper packages like titlesec.

\def\chapter{%
  \if@openright\cleardoublepage\else\clearpage\fi
  \thispagestyle{plain}\global\@topnum\z@
  \@afterindenttrue \secdef\@chapter\@schapter}
\def\@chapter[#1]#2{\refstepcounter{chapter}%
  \ifnum\c@secnumdepth<\z@ \let\@secnumber\@empty
  \else \let\@secnumber\thechapter \fi
  \typeout{\chaptername\space\@secnumber}%
  \def\@toclevel{0}%
  \ifx\chaptername\appendixname \@tocwriteb\tocappendix{chapter}{#2}%
  \else \@tocwriteb\tocchapter{chapter}{#2}\fi
  \chaptermark{#1}%
  \addtocontents{lof}{\protect\addvspace{10\p@}}%
  \addtocontents{lot}{\protect\addvspace{10\p@}}%
  \@makechapterhead{#2}\@afterheading}
\def\@schapter#1{\typeout{#1}%
  \let\@secnumber\@empty
  \def\@toclevel{0}%
  \ifx\chaptername\appendixname \@tocwriteb\tocappendix{chapter}{#1}%
  \else \@tocwriteb\tocchapter{chapter}{#1}\fi
  \chaptermark{#1}%
  \addtocontents{lof}{\protect\addvspace{10\p@}}%
  \addtocontents{lot}{\protect\addvspace{10\p@}}%
  \@makeschapterhead{#1}\@afterheading}

\def\@makechapterhead#1{\global\topskip 7.5pc\relax
  \begingroup
  \fontsize{\@xivpt}{18}\bfseries\centering\iftoggle{boldmathhdr}{ \expandafter \boldmath}{}% %If boldmathhdr is true, make mathematics in chapter headings bold.
    \ifnum\c@secnumdepth>\m@ne
      \leavevmode \hskip-\leftskip
      \rlap{\vbox to\z@{\vss
          \centerline{\normalsize\mdseries
              \uppercase\@xp{\chaptername}\enspace\thechapter}
          \vskip 3pc}}\hskip\leftskip\fi
     #1\par \endgroup
  \skip@34\p@ \advance\skip@-\normalbaselineskip
  \vskip\skip@ }
\def\@makeschapterhead#1{\global\topskip 7.5pc\relax
  \begingroup
  \fontsize{\@xivpt}{18}\bfseries\centering\iftoggle{boldmathhdr}{ \expandafter \boldmath}{}% %If boldmathhdr is true, make mathematics in chapter headings bold.
  #1\par \endgroup
  \skip@34\p@ \advance\skip@-\normalbaselineskip
  \vskip\skip@ }

\def\section{\iftoggle{sectionbreak}{\ifnum\c@section>0{\clearpage}\fi}{}% %If sectionbreak is true, add a clearpage at the end of each section.
  \@startsection{section}{1}%
  \z@{.7\linespacing\@plus\linespacing}{.5\linespacing}%
  {\normalfont%
    \bfseries%
    \centering%
    \iftoggle{boldmathhdr}{ \expandafter \boldmath}{}% %If boldmathhdr is true, make mathematics in section headings bold.
    }}
\def\subsection{\@startsection{subsection}{2}%
  \normalparindent{.5\linespacing\@plus.7\linespacing}{-.5em}%
  {\normalfont%
    \bfseries%
    \iftoggle{boldmathhdr}{ \expandafter \boldmath }{}% %If boldmathhdr is true, make mathematics in subsection headings bold.
  }}
\def\subsubsection{\@startsection{subsubsection}{3}%
  \normalparindent\z@{-.5em}%
  {\normalfont\itshape}}
\def\paragraph{\@startsection{paragraph}{4}%
  \normalparindent\z@{-\fontdimen2\font}%
  \normalfont}
\def\subparagraph{\@startsection{subparagraph}{5}%
  \z@\z@{-\fontdimen2\font}%
  \normalfont}

%%% Local Variables: 
%%% mode: latex
%%% TeX-master: t
%%% End: