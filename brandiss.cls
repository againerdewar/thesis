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

%**************************** Class Options  ************************

%  uncompressed|compressed -> compressed or uncompressed [default] PDF.
%  The uncompressed|compressed option is only meaningful when a PDF is
%  being produced.  If ``uncompressed'' is true, the PDF compression
%  level is set to 0 just before document production begins.  And so
%  ``compressed'' really means ``not uncompressed''.
\newif\if@uncompressed
\DeclareOption{uncompressed}{\@uncompressedtrue}
\DeclareOption{compressed}{\@uncompressedfalse}

% sectionbreak|sectionflow -> break pages after sections or don't
% If ''sectionbreak'' is true, add a \clearpage at the end of each section
\newif\if@sectionbreak
\DeclareOption{sectionbreak}{\@sectionbreaktrue}
\DeclareOption{sectionflow}{\@sectionbreakfalse}

% singlespace|doublespace -> set spacing in relevant places
\newif\if@dodoublespace
\DeclareOption{singlespace}{\@dodoublespacefalse}
\DeclareOption{doublespace}{\@dodoublespacetrue}

% boldmathhdr|normalmathhdr -> use bold math fonts in headers or don't
\newif\if@boldmathhdr
\DeclareOption{boldmathhdr}{\@boldmathhdrtrue}
\DeclareOption{normalmathhdr}{\@boldmathhdrfalse}

%  online|printed -> online or printed [default] submission.
%  Pass these options to the brandiss package.
\DeclareOption{online}{\PassOptionsToPackage{\CurrentOption}{brandiss}}
\DeclareOption{printed}{\PassOptionsToPackage{\CurrentOption}{brandiss}}

%  Default Option: Pass all other options to the amsbook class.
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{amsbook}}

%  Default Setup:
%  Use uncompressed option by default.
\ExecuteOptions{uncompressed}

% Use sectionbreak option by default.
\ExecuteOptions{sectionbreak}

% Use double spacing by default.
\ExecuteOptions{doublespace}

% Use normal math headers by default.
\ExecuteOptions{normalmathhdr}

% GSAS formatting requirements: 12 point font and one-sided printing.
% Set up the amsbook class with these default options before option
% processing so they can be overridden by the passed options.
\PassOptionsToClass{12pt,oneside}{amsbook}

% Process the options.
\ProcessOptions\relax

%********************** Class and Package Loads  *****************

% The amsbook class provides the main document style.
\LoadClass{amsbook}

% Package brandiss provides front page commands.
\RequirePackage{brandiss}[2004/05/05 v1.0 Standard LaTeX package]

% Package ifpdf provides the \ifpdf command.
\RequirePackage{ifpdf}

% Package setspace provides line spacing command.
\RequirePackage{setspace}

% Package geometry sets the margins.  
% REQUIRED: Load before package fancyhdr.
\RequirePackage{geometry}

% Package fancyhdr allows us to set headers and footers.
\RequirePackage{fancyhdr}

% Package hyperref allows links in our PDFs. The 'pdfpagelabels' option gets page labels right in the PDF as well.
\usepackage[pdfpagelabels]{hyperref}

%*********************** Settings and Definitions  ******************

% GSAS formatting requirements: If a PDF document is produced, it
% should not be compressed.
\ifpdf\if@uncompressed\AtBeginDocument{\pdfcompresslevel=0}\fi\fi

% GSAS formatting requirements: The left margin is a minimum of 1.5in.
% The top, bottom, and right margins are a minimum of 1in, except top
% margin of a chapter page is a minimum of 2in.  All printed matter
% fits in these margins.  We set the margings at the GSAS minimum.
% The margins of the first page of a chapter come from the amsbook
% format.
\geometry{
  left=1.5in, right=1in, top=1in, bottom=1in,%% The margins.
  includeheadfoot,%% Header and footer within the margins.
  headheight=3ex,%% Make the headers larger than text and
  headsep=30pt%% separate them from the main text.
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
  \if@dodoublespace\doublespacing\fi
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
  \fontsize{\@xivpt}{18}\bfseries\centering\if@boldmathhdr \expandafter \boldmath \fi% %If boldmathhdr is true, make mathematics in chapter headings bold.
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
  \fontsize{\@xivpt}{18}\bfseries\centering\if@boldmathhdr \expandafter \boldmath \fi% %If boldmathhdr is true, make mathematics in chapter headings bold.
  #1\par \endgroup
  \skip@34\p@ \advance\skip@-\normalbaselineskip
  \vskip\skip@ }

\def\section{\if@sectionbreak{\ifnum\c@section>0{\clearpage}\fi}\fi% %If sectionbreak is true, add a clearpage at the end of each section.
  \@startsection{section}{1}%
  \z@{.7\linespacing\@plus\linespacing}{.5\linespacing}%
  {\normalfont%
    \bfseries%
    \centering%
    \if@boldmathhdr \expandafter \boldmath \fi% %If boldmathhdr is true, make mathematics in section headings bold.
    }}
\def\subsection{\@startsection{subsection}{2}%
  \normalparindent{.5\linespacing\@plus.7\linespacing}{-.5em}%
  {\normalfont%
    \bfseries%
    \if@boldmathhdr \expandafter \boldmath \fi% %If boldmathhdr is true, make mathematics in subsection headings bold.
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

