"""
Desired plots: (x: num_chars (log), y: runtime in ms (log)?)
- Comparison plot of each grammar for the scala-variants and lean
- TODO: Comparison plot of the grammars for lean
- TODO: Some Bar chart bin size diagram for the different grammars?
"""

import argparse

import pandas
from matplotlib import pyplot as plt
from enum import Enum
from dataclasses import dataclass


class Mode(Enum):
    GRAMMAR = "grammar"  # plot all variants for a given grammar
    COMP = "comp"  # plot all grammars for lean


class Grammar(Enum):
    ONE = "1"
    TWO = "2"
    THREE = "3"
    FOUR = "4"
    FIVE = "5"


def grammar_to_bnf(grammar: Grammar) -> str:
    match grammar:
        case Grammar.ONE:
            return "S -> SS | a"
        case Grammar.TWO:
            return "S -> aS | a"
        case Grammar.THREE:
            return "S -> aSa | a"
        case Grammar.FOUR:
            return "S -> Sa | a"
        case Grammar.FIVE:
            return "S -> SX | a, X -> Y | Z, Y -> a, Z -> a"


class Variant(Enum):
    LEAN = "lean"  # There is only one lean impl as of now.
    ISABELLE = "isabelle"  # exported isabelle code
    SCALA_NAIVE = "functional"  # isabelle code handwritten in scala
    SCALA_OPT = "original"  # optimized scala implementation without maintaining pointerinformation


@dataclass
class Experiment:
    variant: Variant
    grammar: Grammar

    def to_filename(self):
        if self.variant is Variant.LEAN:
            return f"lean/lean_grammar={self.grammar.value}.csv"
        else:
            return f"scala/scala_grammar={self.grammar.value}_variant={self.variant.value}.csv"


def plot_grammar(grammar: Grammar):
    fig, ax = plt.subplots()
    experiments = [Experiment(variant=variant, grammar=grammar) for variant in Variant]

    for idx, experiment in enumerate(experiments):
        df = pandas.read_csv(experiment.to_filename())
        n = df["num_chars"].values
        mflops = df["num_miliseconds"].values
        label = f"{experiment.variant.value}"
        if idx == 0:
            marker = "x"
        elif idx == 1:
            marker = "^"
        elif idx == 2:
            marker = "o"
        elif idx == 3:
            marker = "s"
        else:
            assert False, "controlflow issue"

        ax.plot(n, mflops, marker=marker, fillstyle="none", label=label)

    ax.grid(True, linestyle="--")
    ax.set_xlabel("Input length")
    ax.set_ylabel("Duration [ms]")
    # ax.set_xlim(xmin=0, xmax=duration)

    ax.set_xscale("log")
    ax.set_yscale("log")
    # ax.legend(loc="lower right")
    # ax.legend(loc="center right")
    # ax.legend(loc="upper left", bbox_to_anchor=(1, 1))
    ax.legend(loc="upper left")
    # plt.tight_layout()

    ax.set_title(f"Comparison for '{grammar_to_bnf(grammar)}'")
    fig.savefig(f"grammar={grammar.value}.svg", bbox_inches="tight")
    plt.close()


def main():
    parser = argparse.ArgumentParser(description="Plot some measurements")
    parser.add_argument(
        "-g",
        "--grammar",
        help="which grammar to plot",
        required=True,
    )
    parser.add_argument(
        "-m",
        "--mode",
        type=Mode,
        choices=list(Mode),
        help="Lowercase!",
        required=True,
    )
    args = parser.parse_args()
    mode = Mode(args.mode)
    grammar = Grammar(args.grammar)
    if mode is Mode.GRAMMAR:
        plot_grammar(grammar)
    elif mode is Mode.COMP:
        print("Not implemented yet!")


if __name__ == "__main__":
    main()
