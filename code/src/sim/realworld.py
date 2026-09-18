"""The real-world setting of Fig. 5: replay the e-commerce event stream.

    python src/sim/extract.py /tmp/cosmetics/2019-Dec.csv.gz    # -> data/2019-Dec-3types.npz

The paper maps each event timestamp to a 1-second slot and treats that slot as the
event's actual occurrence time. Three event types survive -- `view`, `cart`,
`remove_from_cart` -- and `purchase`, the infrequent one, is dropped. That leaves
1,647,519 occupied slots in the December file against the paper's 1,654,771, the only
reading of the number within half a percent across every month and type subset we
checked. See README, Difference 6.

Replaying the slots rather than fitting a per-type rate and resampling Bernoulli(theta)
matters: burstiness is the one thing a real trace has that U[0,1] does not, and a rate
fit throws it away. The policies are told no more here than in the synthetic setting --
they see the events, and infer Eq. (16)'s geometric age model as usual.
"""
import os

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.abspath(os.path.join(HERE, "..", "..", "data"))
DEFAULT = "2019-Dec-3types.npz"
TYPES = ["view", "cart", "remove_from_cart"]


def load(name=DEFAULT):
    """Returns (theta_hat, stream): the per-slot event rate, and the (3, span) trace."""
    path = os.path.join(DATA, name)
    if not os.path.exists(path):
        raise SystemExit(
            f"{path} is missing. Build it with:\n"
            f"  curl -L -o /tmp/cosmetics.zip "
            f'"https://www.kaggle.com/api/v1/datasets/download/'
            f'mkechinov/ecommerce-events-history-in-cosmetics-shop"\n'
            f"  unzip -d /tmp/cosmetics /tmp/cosmetics.zip\n"
            f"  python src/sim/extract.py /tmp/cosmetics/{name[:8]}.csv.gz"
        )
    z = np.load(path)
    span = int(z["span"])
    stream = np.stack([np.unpackbits(z[t], count=span).astype(bool) for t in TYPES])
    return stream.mean(axis=1), stream
