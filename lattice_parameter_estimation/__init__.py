__version__ = "0.1.0"
__author__ = "Nicolai Krebs"

import sys
import os

file = os.path.abspath(__file__)
here = os.path.dirname(file)

there = os.path.join(here, "estimate_all_schemes")

sys.path.append(here)
sys.path.append(there)

## Logging ##
import logging

# default for library
try:  # Python 2.7+
    from logging import NullHandler
except ImportError:
    class NullHandler(logging.Handler):
        def emit(self, record):
            pass

logger = logging.getLogger(__name__)
logger.addHandler(NullHandler())

# custom logging
class Logging:
    """
    Configuration of logging for lattice estimation.
    """

    @staticmethod
    def set_level(level):
        """Set logging level of library. 

        :param lvl: logging level, e.g. ``logging.DEBUG``
        """
        logger.setLevel(level)
    
    # TODO: add setters for other modules?

    @staticmethod
    def disable_estimation_exception_logging_level():
        logging.getLogger(logger.name + ".problem.estimation_exception_logging").setLevel(logging.CRITICAL)
    
    @staticmethod
    def set_estimation_debug_logging_level(level):
        """Set logging level of estimation execution. 
        
        ``INFO`` shows running algorithm with input parameters and estimation results.
        ``DEBUG`` shows additional information about concurrency and early termination.

        :param lvl: logging level, e.g. ``logging.DEBUG``
        """
        logging.getLogger(logger.name + ".problem.estimation_logging").setLevel(level)
