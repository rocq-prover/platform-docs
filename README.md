# Platform-docs

[![Web_Interface][Web_Interface-shield]][Web_Interface-link]
[![Contributing][contributing-shield]][contributing-link]
[![Zulip][zulip-shield]][zulip-link]

[Web_Interface-shield]: https://img.shields.io/badge/Web_Interface-purple
[Web_Interface-link]: https://www.theozimmermann.net/platform-docs/

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-Green
[contributing-link]: CONTRIBUTING.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20Zulip-blue
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/437203-Platform-docs

The documentation is working with the latesest version of the Rocq Platform.
It is planned in the future to index the documentation and the Rocq Platform's
version and to have a dev version of it, so that users can find docmentation
working for their version of the Rocq and the Platform.
It is not the case as of yet, so the documentation it is not guaranteed to work
perfectly on other versions of Rocq and the Platform, though most of the content
should still be working fine.

## A Collection of Short Interactive Tutorials and How-To Guides for Rocq

This project aims to create an online compilation of short and interactive tutorials and how-to guides for Rocq and the Rocq Platform.

Each core functionality and plugin of Rocq and the Rocq Platform should have (short) pedagogical tutorials and/or
how-to guides demonstrating how to use the functionality, with practical examples.
They should further be available online through an interactive interface, most likely using JSCoq.
There is now a prototype [web interface](https://coq.inria.fr/platform-docs/) to check out.

Tutorials and how-to guides serve different purposes and are complementary.
Tutorials guide a user during learning in discovering specific aspects of a feature like "Notations in Rocq",
by going through (simple) predetermined examples, and introducing notions gradually.
In contrast, how-to guides are use-case-oriented and guides users through real life problems and their inherent complexity,
like "How to define functions by well-founded recursion and reason about them".

For a complete description of the project, you can check out the associated [Rocq Enhancement Proposal](https://github.com/coq/ceps/pull/91).

> [!TIP]
> To gain useful insights about what documentation should be, we recommend
> checking out the website [diataxis](https://diataxis.fr/) that discusses the
> different kind of documentations.
> In particular the [difference between tutorials and how-to](https://diataxis.fr/tutorials-how-to/)
> which are often mistaken.

### Why it is important
- Having an easy to access documentation, accessible through a nice centralized
  online interface is of utmost importance to engage new users, and keep current
  users.
  We can not expect users to have to dig on their own through the reference
  manual, books, or github repositories to learn how to use a particular feature
  that appeals to them.
  Most particularly as these sources may not contain the basic answers they are
  looking for due to their nature.
- Not having such a documentation prevents people from actually discovering and
  learning by themselves new amazing features, as well as the richness of our
  ecosystem.
  Many amazing features are still currently under-documented, and the existing
  documentation is often scattered out.
  A symptom of that is the trouble that students are currently facing to find
  answers or discover new functionalities by themselves.
  Another one, is how often the same questions come up.
- Writing documentation forces us to do stuff right, and consequently to
  understand better features, and their basic applications.
  We hope that by writing the documentation, we will clarify the use of many
  features, and potentially discover bugs.
  Actually, writing tutorials [for Equations](https://github.com/Zimmi48/platform-docs/pull/1#issuecomment-2098810034)
  as already revealed that one of the main features had an unwanted behavior and a bug.
- Most math users are currently unaware of the extent of what has been
  formalised and is available in Rocq.
  There are many libraries, and it is not easy to know which library to use, or
  to know on which axioms they rely or their compatibilities.
  This is obviously not just a documentation issue, but having a clearer
  documentation of what we have and where would help.


### Advantages
Such form of documentation is complementary to other kinds of documentation like the reference manual, and has several advantages:

- Tutorials should enable users to learn and discover specific features on their own, modularly, and according to their needs
- How-tos should provide users practical answers to practical problems that they can refer to when working
- By nature, the documentation should be mostly horizontal, which should:
  - make it easy to navigate and to find specific information
  - prevent users from having to read a bunch of documentation to be able to read a specific tutorial
  - make it possible to build gradually, making new tutorials and how-tos available as we progress
  - allow differentiated learning: depending on your background or objective you can navigate the
    documentation differently, potentially reading different tutorials.
- It will enable us to showcase all that is possible in Rocq's ecosystem
- It should be easy to maintain as once fully written a tutorial or how-to should have any reason to change,
  except if the associated feature or known best practices change.

### Organisation
This project will necessarily have to be a collaborative undertaking considering how much work there is to do,
and the richness and diversity of our ecosystem.
Yet, as the tutorials can mostly be designed independently, by combining the different expertise of the different communities,
there is good hope to quickly get to a good documentation, and we welcome contributions.

As a base for work, we have established an [informal list](draft_structure_doc.md)
of tutorials and how-tos it could be interesting to have.
This list is not fixed and will necessarily evolve through discussions with the community and experience,
but it should already give an idea of the potential of this project.

We will also soon submit a Rocq Enhancement Proposal.

> [!NOTE]
> For more information about project and to participate in disccusions, please checkout on the dedicated [Zulip stream](https://coq.zulipchat.com/#narrow/stream/437203-Platform-docs).
> Among others, you can find there information about [new tutorials and how-tos](https://coq.zulipchat.com/#narrow/stream/437203-Coq-Platform-docs/topic/New.20Tutorials.20and.20How-to.20to.20check.20out), and a [wishlist](https://coq.zulipchat.com/#narrow/stream/437203-Coq-Platform-docs/topic/Wishlist.20Tutorials) to tell us what you need





### How to contribute to the documentation

There is a lot of work to be done before having a comprehensive documentation for Rocq and its Platform, and we welcome contributions.

There are different possible ways to contribute depending on your time and technical skills:
- As user, do not hesitate to gives us feedback on the project on the dedicated [Zulip stream](https://coq.zulipchat.com/#narrow/stream/437203-Platform-docs)
- There is need for regular reviewers to test tutorials, both general ones and expert ones
- There is a lot of tutorials and how-tos to write, both about Rocq and plugins in its Platform
- There is technical work to be done on the (interactive) web interface side

> [!IMPORTANT]
> For more information on how to contribute, please check the [Contribution Guidelines](CONTRIBUTING.md).

### License

The Rocq Platform Docs (in particular, all the text in tutorials and how-to guides) by *The Rocq Platform Docs authors* are licensed under Creative Commons Attribution 4.0 International.
> [!NOTE]
> Code snippets from tutorials and how-to guides can be reused unencumbered.

See [LICENSE.md](LICENSE.md) for details.
