#!/usr/bin/env python3
"""Setup script for DSL Test Generator"""

from setuptools import setup, find_packages
import os
from pathlib import Path

# Read the contents of README file
this_directory = Path(__file__).parent
long_description = (this_directory / "README.md").read_text(encoding='utf-8')

# Read requirements
def read_requirements(filename):
    """Read requirements from file"""
    with open(filename, 'r', encoding='utf-8') as f:
        return [line.strip() for line in f if line.strip() and not line.startswith('#')]

# Get version from __init__.py
def get_version():
    """Extract version from __init__.py"""
    init_file = os.path.join(os.path.dirname(__file__), 'src', '__init__.py')
    with open(init_file, 'r', encoding='utf-8') as f:
        for line in f:
            if line.startswith('__version__'):
                return line.split('=')[1].strip().strip('"').strip("'")
    return '8.0.0'

setup(
    name='dsl-test-generator',
    version=get_version(),
    author='DSL Test Generator Team',
    author_email='contact@dsl-test-generator.com',
    description='A high-quality DSL test generator that automatically generates comprehensive test cases from YAML specifications',
    long_description=long_description,
    long_description_content_type='text/markdown',
    url='https://github.com/hzy-hits/DSL_Z3_testgenerator',
    project_urls={
        'Bug Tracker': 'https://github.com/hzy-hits/DSL_Z3_testgenerator/issues',
        'Documentation': 'https://github.com/hzy-hits/DSL_Z3_testgenerator/blob/main/README.md',
        'Source Code': 'https://github.com/hzy-hits/DSL_Z3_testgenerator',
    },
    license='MIT',
    classifiers=[
        'Development Status :: 5 - Production/Stable',
        'Intended Audience :: Developers',
        'Topic :: Software Development :: Testing',
        'Topic :: Software Development :: Quality Assurance',
        'License :: OSI Approved :: MIT License',
        'Programming Language :: Python :: 3',
        'Programming Language :: Python :: 3.8',
        'Programming Language :: Python :: 3.9',
        'Programming Language :: Python :: 3.10',
        'Programming Language :: Python :: 3.11',
        'Programming Language :: Python :: 3.12',
        'Operating System :: OS Independent',
        'Environment :: Console',
    ],
    keywords='testing, test-generation, dsl, yaml, z3, smt-solver, automated-testing',
    package_dir={'': '.'},
    packages=find_packages(where='.'),
    python_requires='>=3.8',
    install_requires=read_requirements('requirements.txt'),
    extras_require={
        'dev': read_requirements('requirements-dev.txt') if os.path.exists('requirements-dev.txt') else [],
    },
    entry_points={
        'console_scripts': [
            'dsl-test-gen=main:main',
            'dsl-test-generator=main:main',
        ],
    },
    include_package_data=True,
    zip_safe=False,
)