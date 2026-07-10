"""
Desired plots: (x: num_chars (log), y: runtime in ms (log)?)
- Comparison plot of each grammar for the scala-variants and lean
- Comparison plot of the grammars for lean
- Comparison plot of the binsizes for each grammar
"""

import argparse

import pandas
from matplotlib import pyplot as plt
from enum import Enum
from dataclasses import dataclass
from typing import Optional


class Mode(Enum):
    GRAMMAR = "grammar"  # plot all variants for a given grammar
    COMP = "comp"  # plot all grammars for lean
    SIZES = "sizes"  # plot binsizes for each grammar


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


def plot(mode: Mode, grammar: Optional[Grammar]):
    fig, ax = plt.subplots()
    if mode is Mode.GRAMMAR:
        assert (
            grammar is not None
        ), "Called plot with grammar mode, but didnt supply a grammar!"
        experiments = [
            Experiment(variant=variant, grammar=grammar) for variant in Variant
        ]
    else:
        # TODO: Change this to Lean when I've gotten data :)
        variant = Variant.ISABELLE
        experiments = [
            Experiment(variant=variant, grammar=grammar) for grammar in Grammar
        ]

    for idx, experiment in enumerate(experiments):
        df = pandas.read_csv(experiment.to_filename())
        n = df["num_chars"].values
        if mode is Mode.SIZES:
            y = df["num_bins"].values
        else:
            y = df["num_miliseconds"].values
        if mode is Mode.GRAMMAR:
            label = f"{experiment.variant.value}"
        else:
            label = f"{grammar_to_bnf(experiment.grammar)}"
        if idx == 0:
            marker = "x"
        elif idx == 1:
            marker = "^"
        elif idx == 2:
            marker = "o"
        elif idx == 3:
            marker = "s"
        elif idx == 4:
            marker = "v"
        else:
            assert False, "controlflow issue"

        ax.plot(n, y, marker=marker, fillstyle="none", label=label)

    ax.grid(True, linestyle="--")
    ax.set_xlabel("Input length")
    if mode is Mode.SIZES:
        ax.set_ylabel("Total Size of the Bins")
    else:
        ax.set_ylabel("Duration [ms]")
    # ax.set_xlim(xmin=0, xmax=duration)

    ax.set_xscale("log")
    ax.set_yscale("log")
    # ax.legend(loc="center right")
    # ax.legend(loc="upper left", bbox_to_anchor=(1, 1))
    if mode is Mode.SIZES:
        ax.legend(loc="lower right")
    else:
        ax.legend(loc="upper left")
    # plt.tight_layout()

    if mode is Mode.GRAMMAR:
        ax.set_title(f"Runtime of '{grammar_to_bnf(grammar)}'")
        fig.savefig(f"grammar={grammar.value}.svg", bbox_inches="tight")
    elif mode is Mode.COMP:
        ax.set_title(f"Runtime of '{variant.value}'")
        fig.savefig(f"comp_{variant.value}.svg", bbox_inches="tight")
    elif mode is Mode.SIZES:
        ax.set_title(f"Total size of the bins for '{variant.value}'")
        fig.savefig(f"sizes_{variant.value}.svg", bbox_inches="tight")
    plt.close()


def main():
    parser = argparse.ArgumentParser(description="Plot some measurements")
    parser.add_argument(
        "-g",
        "--grammar",
        help="which grammar to plot",
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
    grammar = Grammar(args.grammar) if mode is Mode.GRAMMAR else None
    plot(mode, grammar)


if __name__ == "__main__":
    main()
