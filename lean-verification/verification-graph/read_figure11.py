"""Check the raster inputs to StudyHistogramCounts against the embedded PDF image."""

from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
FIGURE = ROOT.parent / "corrected_thesis" / "fig11.pdf"
CENTERS = (92, 121, 150, 179, 207, 236, 265, 293, 322, 350, 379)


def heights(pixels, top, baseline):
    result = []
    for x in CENTERS:
        for y in range(top, baseline - 1):
            index = 3 * (438 * y + x)
            red, green, blue = pixels[index:index + 3]
            if max(red, green, blue) < 151 or blue - red > 25:
                result.append(baseline - y)
                break
        else:
            result.append(0)
    return result


def main():
    with tempfile.TemporaryDirectory() as temp:
        prefix = Path(temp) / "panel"
        subprocess.run(["pdfimages", str(FIGURE), str(prefix)], check=True)
        ppm = (prefix.parent / "panel-000.ppm").read_bytes()
    magic, width, height, maximum, pixels = ppm.split(maxsplit=4)
    if (magic, width, height, maximum) != (b"P6", b"438", b"429", b"255") or len(pixels) != 438 * 429 * 3:
        raise ValueError("Unexpected embedded image format or dimensions")
    source = (ROOT / "Thesis" / "StudyHistogramCounts.lean").read_text()
    for name, top, baseline in (("figure11ControlHeights", 39, 79), ("figure11PuzzleHeights", 101, 143)):
        found = heights(pixels, top, baseline)
        match = re.search(rf"def {name} .*?!\[([\d, ]+)\]", source)
        if match is None or found != [int(value) for value in match.group(1).split(",")]:
            raise ValueError(f"{name} differs from the figure: {found}")
        print(name, found)


if __name__ == "__main__":
    main()
