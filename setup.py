"""One job that pyproject.toml cannot express.

`packages.find` selects packages; nothing selects individual modules within one.
IsaMini.AoA has to ship `test.py` -- despite the name it is a module, and
`toplevel.py` imports TESTS from it -- while the five `test_*.py` beside it are
pytest files that read AoA/Tests/*.yml, 1019 fixtures no wheel carries. Installed
they could only fail; unfiltered they are half the wheel. `find_package_modules` is
the only hook that can tell the two apart.

Everything else about this build lives in pyproject.toml.
"""

from setuptools import setup
from setuptools.command.build_py import build_py as _build_py


class build_py(_build_py):
    def find_package_modules(self, package, package_dir):
        return [
            entry
            for entry in super().find_package_modules(package, package_dir)
            if not (package == "IsaMini.AoA" and entry[1].startswith("test_"))
        ]


setup(cmdclass={"build_py": build_py})
